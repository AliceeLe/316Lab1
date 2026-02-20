import c0
import pyparsing
from pyparsing import (
    Word, nums, alphas, alphanums, Combine, Literal, Keyword,
    Optional, OneOrMore, ZeroOrMore, Forward, Suppress,
    infixNotation, opAssoc, ParserElement, Regex, QuotedString, Group
)
import re
from typing import List, Tuple

# Enable packrat for performance
ParserElement.enable_packrat()

#
# Automatic Safe Expression Transformation
#
# The verification logic assumes expressions in most command positions cannot crash.
# To keep WLP simple, we hoist potentially unsafe operations (division/modulo and
# array reads) into temporary assignments during parsing.
#
# This is a normalization step internal to the parser; downstream analysis should
# treat the returned AST as already "analysis-ready".
#

class _TempFactory:
    def __init__(self):
        self.counter = 0

    def fresh(self) -> str:
        self.counter += 1
        # User identifiers cannot start with '_' (see Ident in grammar), so this
        # cannot clash with source variables.
        return f"_t{self.counter}"


def _hoist_exp(e: c0.Exp, tf: _TempFactory) -> Tuple[c0.Exp, List[c0.Stmt]]:
    """
    Hoist expression `e` into (safe_e, setup_stmts) where safe_e contains no
    array reads and no division/modulo, and setup_stmts performs the necessary
    intermediate computations (including the safety-checked operations).
    """
    match e:
        case c0.IntConst(_) | c0.BoolConst(_) | c0.NullConst() | c0.Var(_) | c0.ResultVar():
            return e, []

        case c0.BinOp(op, l, r):
            sl, al = _hoist_exp(l, tf)
            sr, ar = _hoist_exp(r, tf)
            setup = al + ar
            if op in ["/", "%"]:
                tmp = tf.fresh()
                setup.append(c0.Decl(c0.IntType(), tmp, None))
                setup.append(c0.Assign(tmp, c0.BinOp(op, sl, sr)))
                return c0.Var(tmp), setup
            return c0.BinOp(op, sl, sr), setup

        case c0.UnOp(op, arg):
            sa, aa = _hoist_exp(arg, tf)
            return c0.UnOp(op, sa), aa

        case c0.Length(arg):
            sa, aa = _hoist_exp(arg, tf)
            return c0.Length(sa), aa

        case c0.ArrayAccess(arr, idx):
            sarr, aarr = _hoist_exp(arr, tf)
            sidx, aidx = _hoist_exp(idx, tf)
            setup = aarr + aidx
            tmp = tf.fresh()
            setup.append(c0.Decl(c0.IntType(), tmp, None))
            setup.append(c0.ArrRead(tmp, sarr, sidx))
            return c0.Var(tmp), setup

        case _:
            return e, []


def _as_stmt(stmts: List[c0.Stmt]) -> c0.Stmt:
    if not stmts:
        return c0.Block([])
    if len(stmts) == 1:
        return stmts[0]
    return c0.Block(stmts)


def _normalize_stmt_list(stmt: c0.Stmt, tf: _TempFactory) -> List[c0.Stmt]:
    match stmt:
        case c0.Decl(typ, name, init):
            if init is None:
                return [stmt]
            si, ai = _hoist_exp(init, tf)
            return ai + [c0.Decl(typ, name, si)]

        case c0.Assign(dest, src):
            ss, aa = _hoist_exp(src, tf)
            return aa + [c0.Assign(dest, ss)]

        case c0.ArrWrite(arr, idx, val):
            sa, aa = _hoist_exp(arr, tf)
            si, ai = _hoist_exp(idx, tf)
            sv, av = _hoist_exp(val, tf)
            return aa + ai + av + [c0.ArrWrite(sa, si, sv)]

        case c0.If(cond, true_branch, false_branch):
            sc, ac = _hoist_exp(cond, tf)
            tb = _as_stmt(_normalize_stmt_list(true_branch, tf))
            fb = _as_stmt(_normalize_stmt_list(false_branch, tf)) if false_branch else None
            return ac + [c0.If(sc, tb, fb)]

        case c0.While(cond, invs, body):
            sc, ac = _hoist_exp(cond, tf)
            # Recompute the condition temporaries at the end of each iteration.
            # IMPORTANT: do not redeclare temporaries inside the loop body.
            recompute = [s for s in ac if not isinstance(s, c0.Decl)]
            body_stmt = _as_stmt(_normalize_stmt_list(body, tf))
            if isinstance(body_stmt, c0.Block):
                new_body = c0.Block(body_stmt.stmts + recompute)
            else:
                new_body = c0.Block([body_stmt] + recompute)
            return ac + [c0.While(sc, invs, new_body)]

        case c0.Block(stmts):
            new_stmts: List[c0.Stmt] = []
            for s in stmts:
                new_stmts.extend(_normalize_stmt_list(s, tf))
            return [c0.Block(new_stmts)]

        case c0.Assert(cond):
            sc, ac = _hoist_exp(cond, tf)
            return ac + [c0.Assert(sc)]

        case c0.Return(val):
            if val is None:
                return [stmt]
            sv, av = _hoist_exp(val, tf)
            return av + [c0.Return(sv)]

        case c0.AllocArray(dest, typ, count):
            sc, ac = _hoist_exp(count, tf)
            return ac + [c0.AllocArray(dest, typ, sc)]

        case _:
            return [stmt]


def _normalize_program(prog: c0.Program) -> c0.Program:
    tf = _TempFactory()
    new_stmts: List[c0.Stmt] = []
    for s in prog.stmts:
        new_stmts.extend(_normalize_stmt_list(s, tf))
    return c0.Program(stmts=new_stmts, requires=prog.requires, ensures=prog.ensures, args=prog.args)


def file_parse(text: str) -> c0.Program:
    NormalComment = Regex(r"//(?![@]).*")
    BlockComment = Regex(r"/\*.*?\*/", flags=re.DOTALL)

    # Keywords
    INT = Keyword("int")
    BOOL = Keyword("bool") # Added bool support
    TRUE = Keyword("true")
    FALSE = Keyword("false")
    NULL = Keyword("NULL")
    ALLOC_ARRAY = Keyword("alloc_array")
    LENGTH = Literal("\\length")
    IF = Keyword("if")
    ELSE = Keyword("else")
    WHILE = Keyword("while")
    ASSERT = Keyword("assert")
    ERROR = Keyword("error")
    RETURN = Keyword("return")
    
    # Contract keywords
    ANNOTATION_START = Literal("//@")
    LOOP_INVARIANT = Keyword("loop_invariant")
    C_ASSERT = Keyword("assert") 
    REQUIRES = Keyword("requires")
    ENSURES = Keyword("ensures")

    # Punctuation
    LPAREN = Suppress("(")
    RPAREN = Suppress(")")
    LBRACE = Suppress("{")
    RBRACE = Suppress("}")
    LBRACKET = Suppress("[")
    RBRACKET = Suppress("]")
    SEMI = Suppress(";")
    COMMA = Suppress(",")
    ASSIGN_OP = Literal("=")

    # Identifiers
    Ident = Word(alphas, alphanums + "_")
    Reserved = INT | BOOL | TRUE | FALSE | NULL | ALLOC_ARRAY | LENGTH | IF | ELSE | WHILE | ASSERT | ERROR | RETURN | REQUIRES | ENSURES | LOOP_INVARIANT | Keyword("main")
    
    # Use NON-RESERVED identifier for variables
    Identifier = (~Reserved + Ident).setParseAction(lambda t: t[0])
    
    # Must use copy() to avoid mutating Identifier which is used elsewhere as string
    VarIdent = Identifier.copy().setParseAction(lambda t: c0.Var(t[0]))
    
    # Types: int, bool, int[] (no pointers/structs; no multi-dimensional arrays)
    Type = Forward()
    IntType = INT.setParseAction(lambda _: c0.IntType())
    BoolType = BOOL.setParseAction(lambda _: c0.BoolType())
    IntArrayType = (INT + Literal("[]")).setParseAction(lambda _: c0.ArrayType(c0.IntType()))
    Type <<= (IntArrayType | IntType | BoolType)

    # Forward declarations
    SafeExp = Forward()
    LogicExp = Forward()
    Stmt = Forward()

    # --- Safe Expressions (No memory access) ---
    SafeInt = Word(nums).setParseAction(lambda t: c0.IntConst(int(t[0])))
    SafeBool = (TRUE | FALSE).setParseAction(lambda t: c0.BoolConst(t[0] == "true"))

    def _reject_null(s: str, loc: int, _toks):
        raise pyparsing.ParseFatalException(s, loc, "NULL is not supported (no pointers in this subset)")
    
    SafeAtom = (
        SafeInt |
        SafeBool | 
        VarIdent |
        (LPAREN + SafeExp + RPAREN)
    )

    def binop(op, cls=c0.BinOp):
        return lambda t: cls(op, t[0][0], t[0][2])
    
    def make_binop(t):
        tokens = t[0]
        res = tokens[0]
        i = 1
        while i < len(tokens):
            op = tokens[i]
            rhs = tokens[i+1]
            res = c0.BinOp(op, res, rhs)
            i += 2
        return res

    # L0_Logic handles array access: Atom [ exp ] [ exp ]
    # We rename this concept to be usable in SafeExp too

    RESULT = Literal("\\result")
    ResultAtom = RESULT.setParseAction(lambda _: c0.ResultVar())
    
    # 1. Base Atoms (ints, bools, null, vars, parenthesis, \result (contracts))
    BadNULL = NULL.setParseAction(_reject_null)
    BaseAtom = (
        SafeInt | SafeBool | BadNULL | ResultAtom | VarIdent | (LPAREN + LogicExp + RPAREN)
    )
    
    # 2. Add Array Access: Atom[idx][idx]...
    def reduce_index(t):
        res = t[0]
        for i in range(1, len(t)):
            res = c0.ArrayAccess(res, t[i])
        return res

    AtomWithArray = (BaseAtom + ZeroOrMore(LBRACKET + LogicExp + RBRACKET)).setParseAction(
        lambda t: reduce_index(t)
    )
    
    def make_unop(t):
        op = t[0][0]
        arg = t[0][1]
        if op == "\\length": return c0.Length(arg)
        return c0.UnOp(op, arg)
    
    # Precedence for SafeExp
    SafeExp <<= infixNotation(AtomWithArray, [
        (Literal("!") | LENGTH, 1, opAssoc.RIGHT, make_unop),
        (Literal("-"), 1, opAssoc.RIGHT, make_unop),
        (Literal("*") | Literal("/") | Literal("%"), 2, opAssoc.LEFT, make_binop),
        (Literal("+") | Literal("-"), 2, opAssoc.LEFT, make_binop),
        (Literal("<=") | Literal(">=") | Literal("<") | Literal(">"), 2, opAssoc.LEFT, make_binop),
        (Literal("==") | Literal("!="), 2, opAssoc.LEFT, make_binop),
        (Literal("&&"), 2, opAssoc.LEFT, make_binop),
        (Literal("||"), 2, opAssoc.LEFT, make_binop),
    ])

    # L1: Unary !, -, \length (prefix)
    def make_unary_logic(t):
        ops = t[:-1]
        arg = t[-1]
        for op in reversed(ops):
            if op == "!": arg = c0.UnOp("!", arg)
            elif op == "-": arg = c0.UnOp("-", arg)
            elif op == "\\length": arg = c0.Length(arg)
        return arg

    FORALL = Literal("\\forall")

    L1_Logic = Forward()
    
    # In quantifiers, we only support integer bound variables.
    Quantifier = (FORALL + INT + Identifier + Suppress(Literal(".")) + LogicExp).setParseAction(
        lambda t: c0.ForAll([t[2]], t[3])
    )
    
    # L1_Logic builds on AtomWithArray and Quantifier.
    # Note: AtomWithArray also supports \result[...] (contracts).
    L1_Logic <<= (ZeroOrMore(Literal("!") | Literal("-") | LENGTH) + 
                  (Quantifier | AtomWithArray)
                 ).setParseAction(make_unary_logic)

    LogicExp <<= infixNotation(L1_Logic, [
        (Literal("*") | Literal("/") | Literal("%"), 2, opAssoc.LEFT, make_binop),
        (Literal("+") | Literal("-"), 2, opAssoc.LEFT, make_binop),
        (Literal("<=") | Literal(">=") | Literal("<") | Literal(">"), 2, opAssoc.LEFT, make_binop),
        (Literal("==") | Literal("!="), 2, opAssoc.LEFT, make_binop),
        (Literal("&&"), 2, opAssoc.LEFT, make_binop),
        (Literal("||"), 2, opAssoc.LEFT, make_binop),
        (Literal("=>"), 2, opAssoc.RIGHT, make_binop),
    ])

    # --- Statements ---
    
    # SafeExp is deprecated; use LogicExp for everything.
    # We still define SafeExp as an alias to LogicExp just in case, but grammar uses LogicExp.
    SafeExp = LogicExp 

    # --- Statements ---
    
    # Statement handling improvements
    def flatten(t):
        res = []
        for x in t:
            if isinstance(x, list): res.extend(flatten(x))
            else: res.append(x)
        return res

    DeclStmt = (Type + Identifier + Optional(ASSIGN_OP + LogicExp) + SEMI).setParseAction(
        lambda t: c0.Decl(t[0], t[1], t[3] if len(t) > 3 else None)
    )
    
    # Handle int[] x = alloc_array(...)
    # Tokens: Type, Ident, =, alloc_array, Type, SafeExp
    DeclAllocStmt = (Type + Identifier + ASSIGN_OP + ALLOC_ARRAY + LPAREN + INT + COMMA + LogicExp + RPAREN + SEMI).setParseAction(
        lambda t: [c0.Decl(t[0], t[1], None), c0.AllocArray(t[1], c0.IntType(), t[5])]
    )
    
    def make_assign(t):
        lhs = t[0]
        rhs = t[2]
        if isinstance(lhs, c0.Var):
            return c0.Assign(lhs.name, rhs)
        elif isinstance(lhs, c0.ArrayAccess):
            return c0.ArrWrite(lhs.arr, lhs.index, rhs)
        else:
             raise pyparsing.ParseException(f"Invalid assignment target: {lhs}")

    AssignStmt = (AtomWithArray + ASSIGN_OP + LogicExp + SEMI).setParseAction(make_assign)
    
    # Tokens: Ident, =, alloc_array, Type, count
    AllocArrayStmt = (Identifier + ASSIGN_OP + ALLOC_ARRAY + LPAREN + INT + COMMA + LogicExp + RPAREN + SEMI).setParseAction(
        lambda t: c0.AllocArray(t[0], c0.IntType(), t[4])
    )
    
    Block = (LBRACE - ZeroOrMore(Stmt) + RBRACE).setParseAction(
        lambda t: c0.Block(flatten(t)) # Flatten nested lists from DeclAlloc
    )
    
    IfStmt = (IF - LPAREN + LogicExp + RPAREN + Stmt + Optional(ELSE + Stmt)).setParseAction(
        lambda t: c0.If(t[1], t[2], t[4] if len(t) > 4 else None)
    )
    
    WhileStmt = (WHILE - LPAREN + LogicExp + RPAREN + 
                 ZeroOrMore((ANNOTATION_START + LOOP_INVARIANT + LogicExp + SEMI).setParseAction(lambda t: t[2])) + 
                 Stmt).setParseAction(
        lambda t: c0.While(t[1], list(t[2:-1]), t[-1])
    )
    
    AssertStmt = (ASSERT + LPAREN + LogicExp + RPAREN + SEMI).setParseAction(
        lambda t: c0.Assert(t[1])
    )
    
    ContractAssertStmt = (ANNOTATION_START + C_ASSERT + LogicExp + SEMI).setParseAction(
        lambda t: c0.Assert(t[2])
    )
    
    StringLit = QuotedString('"')
    ErrorStmt = (ERROR + LPAREN + StringLit + RPAREN + SEMI).setParseAction(
        lambda t: c0.Error(t[1])
    )

    ReturnStmt = (RETURN + LogicExp + SEMI).setParseAction(
        lambda t: c0.Return(t[1])
    )
    
    Stmt <<= (
        Block |
        DeclAllocStmt | # Must come before DeclStmt? Or parallel? DeclStmt matches identifier assignment.
        DeclStmt |
        IfStmt | 
        WhileStmt |
        AssertStmt |
        ContractAssertStmt |
        ErrorStmt |
        ReturnStmt |
        AllocArrayStmt |
        AssignStmt
    )

    ContractRaw = Group(ANNOTATION_START + (REQUIRES | ENSURES)("kind") + LogicExp("cond") + SEMI)
    
    def _is_int_type(typ: c0.Type) -> bool:
        return isinstance(typ, c0.IntType)

    def _is_int_array_type(typ: c0.Type) -> bool:
        return isinstance(typ, c0.ArrayType) and isinstance(typ.base, c0.IntType)

    def _exp_contains_result(e: c0.Exp) -> bool:
        match e:
            case c0.ResultVar():
                return True
            case c0.BinOp(_, l, r):
                return _exp_contains_result(l) or _exp_contains_result(r)
            case c0.UnOp(_, a) | c0.Length(a):
                return _exp_contains_result(a)
            case c0.ArrayAccess(a, i):
                return _exp_contains_result(a) or _exp_contains_result(i)
            case c0.ForAll(_, body):
                return _exp_contains_result(body)
            case _:
                return False

    def _stmt_contains_result(s: c0.Stmt) -> bool:
        match s:
            case c0.Decl(_, _, init):
                return init is not None and _exp_contains_result(init)
            case c0.Assign(_, src):
                return _exp_contains_result(src)
            case c0.AllocArray(_, _, count):
                return _exp_contains_result(count)
            case c0.ArrRead(_, arr, idx):
                return _exp_contains_result(arr) or _exp_contains_result(idx)
            case c0.ArrWrite(arr, idx, val):
                return _exp_contains_result(arr) or _exp_contains_result(idx) or _exp_contains_result(val)
            case c0.Assert(cond):
                return _exp_contains_result(cond)
            case c0.If(cond, t, f):
                return _exp_contains_result(cond) or _stmt_contains_result(t) or (f is not None and _stmt_contains_result(f))
            case c0.While(cond, invs, body):
                return _exp_contains_result(cond) or any(_exp_contains_result(i) for i in invs) or _stmt_contains_result(body)
            case c0.Block(stmts):
                return any(_stmt_contains_result(x) for x in stmts)
            case c0.Return(val):
                return val is not None and _exp_contains_result(val)
            case _:
                return False

    def _stmt_contains_return(s: c0.Stmt) -> bool:
        match s:
            case c0.Return(_):
                return True
            case c0.Block(stmts):
                return any(_stmt_contains_return(x) for x in stmts)
            case c0.If(_, t, f):
                return _stmt_contains_return(t) or (f is not None and _stmt_contains_return(f))
            case c0.While(_, _, body):
                return _stmt_contains_return(body)
            case _:
                return False

    def _is_len_result(e: c0.Exp) -> bool:
        return isinstance(e, c0.Length) and isinstance(e.arg, c0.ResultVar)

    def _is_result_only_in_len_result(e: c0.Exp) -> bool:
        match e:
            case c0.ResultVar():
                return False
            case c0.Length(arg):
                # \length(\result) is allowed, but other nested uses are checked below.
                return isinstance(arg, c0.ResultVar) or _is_result_only_in_len_result(arg)
            case c0.BinOp(_, l, r):
                return _is_result_only_in_len_result(l) and _is_result_only_in_len_result(r)
            case c0.UnOp(_, a):
                return _is_result_only_in_len_result(a)
            case c0.ArrayAccess(a, i):
                return _is_result_only_in_len_result(a) and _is_result_only_in_len_result(i)
            case c0.ForAll(_, body):
                return _is_result_only_in_len_result(body)
            case _:
                return True

    def _is_len_result_eq(e: c0.Exp) -> bool:
        match e:
            case c0.BinOp("==", l, r):
                if _is_len_result(l) and _is_result_only_in_len_result(r):
                    return True
                if _is_len_result(r) and _is_result_only_in_len_result(l):
                    return True
                return False
            case _:
                return False

    def parse_main(s: str, loc: int, t):
        # Enforce: int[] main(int argc, int[] in)
        if not _is_int_array_type(t.ret_type):
            raise pyparsing.ParseFatalException(s, loc, "main must return int[]")
        if not _is_int_type(t.argc_type) or t.argc_name != "argc":
            raise pyparsing.ParseFatalException(
                s,
                loc,
                f"first argument must be `int argc` (got `{t.argc_type} {t.argc_name}`)",
            )
        if not _is_int_array_type(t.in_type) or t.in_name != "in":
            raise pyparsing.ParseFatalException(
                s,
                loc,
                f"second argument must be `int[] in` (got `{t.in_type} {t.in_name}`)",
            )

        stmts = t.body.stmts

        # Exactly one return, at top-level end of main body.
        if len(stmts) == 0 or not isinstance(stmts[-1], c0.Return):
            raise pyparsing.ParseFatalException(s, loc, "main must end with a single top-level return statement")
        for st in stmts[:-1]:
            if _stmt_contains_return(st):
                raise pyparsing.ParseFatalException(s, loc, "main must contain exactly one return statement at top level")

        # \result may only appear in contracts, not in executable statements.
        for st in stmts:
            if _stmt_contains_result(st):
                raise pyparsing.ParseFatalException(s, loc, "\\result is only allowed in contracts")

        reqs = []
        ens = []
        for c in t.contracts:
            if c.kind == "requires":
                reqs.append(c.cond)
            elif c.kind == "ensures":
                ens.append(c.cond)

        if not ens:
            raise pyparsing.ParseFatalException(
                s,
                loc,
                "main must include at least one ensures of the form `\\length(\\result) == ...`",
            )
        if not any(_is_len_result_eq(e) for e in ens):
            raise pyparsing.ParseFatalException(
                s,
                loc,
                "main must include an ensures that exactly specifies the return length: `\\length(\\result) == ...`",
            )

        return c0.Program(stmts, requires=reqs, ensures=ens, args=[t.argc_name, t.in_name])

    MainFunc = (
        Type("ret_type") + Keyword("main") - LPAREN +
        Type("argc_type") + Identifier("argc_name") + COMMA +
        Type("in_type") + Identifier("in_name") + RPAREN +
        ZeroOrMore(ContractRaw)("contracts") +
        Block("body")
    ).setParseAction(parse_main)

    # Program must be exactly the single main function (comments/whitespace allowed around it).
    ProgramParser = MainFunc
    
    ProgramParser.ignore(NormalComment)
    ProgramParser.ignore(BlockComment)
    
    try:
        prog = ProgramParser.parseString(text, parseAll=True)[0]
        prog = _normalize_program(prog)
        _typecheck_and_validate_program(text, prog)
        return prog
    except pyparsing.ParseException as e:
        print(f"Parse Error at line {e.lineno}, column {e.col}:")
        print(e.line)
        print(" " * (e.col - 1) + "^")
        print(f"Message: {e.msg}")
        raise e


def _typecheck_and_validate_program(src: str, prog: c0.Program) -> None:
    """
    Enforce lab-specific syntactic restrictions and basic type checks.

    This includes the "no array aliasing" rule: `int[]` variables are not
    assignable (except via `alloc_array` or indexed writes `A[i] = e`).
    """

    def fatal(msg: str) -> None:
        # The AST does not carry source locations; use loc=0 and a clear message.
        raise pyparsing.ParseFatalException(src, 0, msg)

    def is_int(t: c0.Type) -> bool:
        return isinstance(t, c0.IntType)

    def is_bool(t: c0.Type) -> bool:
        return isinstance(t, c0.BoolType)

    def is_int_array(t: c0.Type) -> bool:
        return isinstance(t, c0.ArrayType) and isinstance(t.base, c0.IntType)

    def lookup(env_stack: list[dict[str, c0.Type]], name: str) -> c0.Type:
        for env in reversed(env_stack):
            if name in env:
                return env[name]
        fatal(f"use of undeclared variable `{name}`")
        raise AssertionError("unreachable")

    def exp_type(env_stack: list[dict[str, c0.Type]], e: c0.Exp) -> c0.Type:
        match e:
            case c0.IntConst(_):
                return c0.IntType()
            case c0.BoolConst(_):
                return c0.BoolType()
            case c0.Var(name):
                return lookup(env_stack, name)
            case c0.ResultVar():
                return c0.ArrayType(c0.IntType())

            case c0.Length(arg):
                t_arg = exp_type(env_stack, arg)
                if not is_int_array(t_arg):
                    fatal("\\length expects an `int[]` expression")
                return c0.IntType()

            case c0.ArrayAccess(arr, idx):
                t_arr = exp_type(env_stack, arr)
                t_idx = exp_type(env_stack, idx)
                if not is_int_array(t_arr):
                    fatal("array indexing expects an `int[]` base expression")
                if not is_int(t_idx):
                    fatal("array index must have type `int`")
                return c0.IntType()

            case c0.UnOp(op, arg):
                t_arg = exp_type(env_stack, arg)
                if op == "!":
                    if not is_bool(t_arg):
                        fatal("`!` expects a `bool` operand")
                    return c0.BoolType()
                if op == "-":
                    if not is_int(t_arg):
                        fatal("unary `-` expects an `int` operand")
                    return c0.IntType()
                fatal(f"unknown unary operator `{op}`")
                raise AssertionError("unreachable")

            case c0.BinOp(op, l, r):
                t_l = exp_type(env_stack, l)
                t_r = exp_type(env_stack, r)

                arith = {"+", "-", "*", "/", "%"}
                cmp_ops = {"<", "<=", ">", ">="}
                logic = {"&&", "||", "=>"}
                eq = {"==", "!="}

                if op in arith:
                    if not (is_int(t_l) and is_int(t_r)):
                        fatal(f"`{op}` expects `int` operands")
                    return c0.IntType()
                if op in cmp_ops:
                    if not (is_int(t_l) and is_int(t_r)):
                        fatal(f"`{op}` expects `int` operands")
                    return c0.BoolType()
                if op in logic:
                    if not (is_bool(t_l) and is_bool(t_r)):
                        fatal(f"`{op}` expects `bool` operands")
                    return c0.BoolType()
                if op in eq:
                    if type(t_l) is not type(t_r):
                        fatal(f"`{op}` expects operands of the same type")
                    return c0.BoolType()

                fatal(f"unknown binary operator `{op}`")
                raise AssertionError("unreachable")

            case c0.ForAll(vars, body):
                # \forall introduces int-bound variables.
                new_env = dict(env_stack[-1])
                for v in vars:
                    new_env[v] = c0.IntType()
                t_body = exp_type(env_stack[:-1] + [new_env], body)
                if not is_bool(t_body):
                    fatal("\\forall body must be a boolean formula")
                return c0.BoolType()

            case _:
                fatal(f"unsupported expression form: {type(e)}")
                raise AssertionError("unreachable")

    def check_stmt(env_stack: list[dict[str, c0.Type]], s: c0.Stmt) -> None:
        match s:
            case c0.Decl(typ, name, init):
                if is_int_array(typ) and init is not None:
                    fatal("`int[]` variables cannot be initialized by assignment; use `alloc_array`")
                if init is not None:
                    t_init = exp_type(env_stack, init)
                    if type(t_init) is not type(typ):
                        fatal(f"type mismatch in initializer for `{name}`")
                env_stack[-1][name] = typ

            case c0.Assign(dest, src):
                t_dest = lookup(env_stack, dest)
                if is_int_array(t_dest):
                    fatal("assignment between `int[]` variables is not allowed (use `alloc_array` or indexed assignment)")
                t_src = exp_type(env_stack, src)
                if type(t_src) is not type(t_dest):
                    fatal(f"type mismatch in assignment to `{dest}`")

            case c0.AllocArray(dest, typ, count):
                t_dest = lookup(env_stack, dest)
                if not is_int_array(t_dest):
                    fatal("`alloc_array` destination must have type `int[]`")
                if not isinstance(typ, c0.IntType):
                    fatal("only `alloc_array(int, n)` is supported")
                if not is_int(exp_type(env_stack, count)):
                    fatal("`alloc_array` count must have type `int`")

            case c0.ArrWrite(arr, idx, val):
                if not isinstance(arr, c0.Var):
                    fatal("array assignment must have the form `A[i] = e` where `A` is a variable")
                t_arr = lookup(env_stack, arr.name)
                if not is_int_array(t_arr):
                    fatal("array assignment expects an `int[]` base variable")
                if not is_int(exp_type(env_stack, idx)):
                    fatal("array index must have type `int`")
                if not is_int(exp_type(env_stack, val)):
                    fatal("array element value must have type `int`")

            case c0.ArrRead(dest, arr, idx):
                if not is_int(lookup(env_stack, dest)):
                    fatal("array read destination must have type `int`")
                if not is_int_array(exp_type(env_stack, arr)):
                    fatal("array indexing expects an `int[]` value")
                if not is_int(exp_type(env_stack, idx)):
                    fatal("array index must have type `int`")

            case c0.If(cond, t, f):
                if not is_bool(exp_type(env_stack, cond)):
                    fatal("`if` condition must have type `bool`")
                env_stack.append({})
                check_stmt(env_stack, t)
                env_stack.pop()
                if f is not None:
                    env_stack.append({})
                    check_stmt(env_stack, f)
                    env_stack.pop()

            case c0.While(cond, invs, body):
                if not is_bool(exp_type(env_stack, cond)):
                    fatal("`while` condition must have type `bool`")
                for inv in invs:
                    if not is_bool(exp_type(env_stack, inv)):
                        fatal("loop invariants must have type `bool`")
                env_stack.append({})
                check_stmt(env_stack, body)
                env_stack.pop()

            case c0.Block(stmts):
                env_stack.append({})
                for st in stmts:
                    check_stmt(env_stack, st)
                env_stack.pop()

            case c0.Assert(cond):
                if not is_bool(exp_type(env_stack, cond)):
                    fatal("`assert` condition must have type `bool`")

            case c0.Return(val):
                if val is None:
                    fatal("main must return an `int[]` expression")
                if not is_int_array(exp_type(env_stack, val)):
                    fatal("main must return an `int[]` expression")

            case c0.Error(_):
                return

            case _:
                fatal(f"unsupported statement form: {type(s)}")

    env_stack: list[dict[str, c0.Type]] = [{}]
    if prog.args and len(prog.args) == 2:
        argc_name, in_name = prog.args
        env_stack[-1][argc_name] = c0.IntType()
        env_stack[-1][in_name] = c0.ArrayType(c0.IntType())

    for e in (prog.requires or []):
        if not is_bool(exp_type(env_stack, e)):
            fatal("requires clauses must be boolean formulas")
    for e in (prog.ensures or []):
        if not is_bool(exp_type(env_stack, e)):
            fatal("ensures clauses must be boolean formulas")

    for st in prog.stmts:
        check_stmt(env_stack, st)
