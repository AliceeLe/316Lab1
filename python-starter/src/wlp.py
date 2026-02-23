from __future__ import annotations

from typing import List, Dict, Tuple

import c0
import c0_util
import solver

# Expression helpers
def _true() -> c0.Exp:  return c0.BoolConst(True)
def _false() -> c0.Exp: return c0.BoolConst(False)

def _and(a: c0.Exp, b: c0.Exp) -> c0.Exp:
    if isinstance(a, c0.BoolConst) and a.value:      return b
    if isinstance(b, c0.BoolConst) and b.value:      return a
    if isinstance(a, c0.BoolConst) and not a.value:  return a
    if isinstance(b, c0.BoolConst) and not b.value:  return b
    return c0.BinOp("&&", a, b)

def _implies(a: c0.Exp, b: c0.Exp) -> c0.Exp:
    return c0.BinOp("=>", a, b)

def _not(a: c0.Exp) -> c0.Exp:
    return c0.UnOp("!", a)

def _int(v: int) -> c0.Exp:
    return c0.IntConst(v)

def _le(a: c0.Exp, b: c0.Exp) -> c0.Exp:
    return c0.BinOp("<=", a, b)

def _lt(a: c0.Exp, b: c0.Exp) -> c0.Exp:
    return c0.BinOp("<", a, b)

def _len(a: c0.Exp) -> c0.Exp:
    return c0.Length(a)

def _neq(a: c0.Exp, b: c0.Exp) -> c0.Exp:
    return c0.BinOp("!=", a, b)


# Division/modulo safety guard
def divmod_guard(e: c0.Exp) -> c0.Exp:
    match e:
        case c0.BinOp(op, left, right):
            g = _and(divmod_guard(left), divmod_guard(right))
            if op in ("/", "%"):
                g = _and(g, _neq(right, _int(0)))
            return g
        case c0.UnOp(_, arg):
            return divmod_guard(arg)
        case c0.ArrayAccess(arr, index):
            return _and(divmod_guard(arr), divmod_guard(index))
        case c0.Length(arg):
            return divmod_guard(arg)
        case c0.ArrMake(length):
            return divmod_guard(length)
        case c0.ArrSet(arr, index, val):
            return _and(
                _and(divmod_guard(arr), divmod_guard(index)),
                divmod_guard(val),
            )
        case c0.ForAll(_, body):
            return divmod_guard(body)
        case _:
            return _true()


def _normalize_length(e: c0.Exp) -> c0.Exp:
    match e:
        case c0.Length(c0.ArrSet(arr, _, _)):
            return _normalize_length(c0.Length(arr))
        case c0.Length(arg):
            return c0.Length(_normalize_length(arg))
        case c0.BinOp(op, l, r):
            return c0.BinOp(op, _normalize_length(l), _normalize_length(r))
        case c0.UnOp(op, arg):
            return c0.UnOp(op, _normalize_length(arg))
        case c0.ArrayAccess(arr, idx):
            return c0.ArrayAccess(_normalize_length(arr), _normalize_length(idx))
        case c0.ArrSet(arr, idx, val):
            return c0.ArrSet(
                _normalize_length(arr), _normalize_length(idx), _normalize_length(val)
            )
        case c0.ArrMake(length):
            return c0.ArrMake(_normalize_length(length))
        case c0.ForAll(vs, body):
            return c0.ForAll(vs, _normalize_length(body))
        case _:
            return e


# Module-level type environment

_var_types: Dict[str, c0.Type] = {}


def collect_types(prog: c0.Program) -> Dict[str, c0.Type]:
    """Collect name->Type for every variable so solver encodes arrays correctly."""
    types: Dict[str, c0.Type] = {}
    arg_names = prog.args or []
    for name, typ in zip(arg_names, [c0.IntType(), c0.ArrayType(c0.IntType())]):
        types[name] = typ

    def walk(s: c0.Stmt) -> None:
        match s:
            case c0.Decl(typ, name, _):       types[name] = typ
            case c0.AllocArray(dest, typ, _):  types[dest] = c0.ArrayType(typ)
            case c0.ArrRead(dest, _, _):       types[dest] = c0.IntType()
            case c0.Block(stmts):
                for st in stmts: walk(st)
            case c0.If(_, t, f):
                walk(t)
                if f: walk(f)
            case c0.While(_, _, body):
                walk(body)

    for s in prog.stmts:
        walk(s)
    return types


def _register_types(extra: Dict[str, c0.Type]) -> None:
    _var_types.update(extra)
    solver.set_var_types(_var_types)

WhiteBox = List[c0.Exp] 


def wlp(stmt: c0.Stmt, Q: c0.Exp, depth: int = 0) -> Tuple[c0.Exp, WhiteBox]:
    match stmt:

        case c0.Block(stmts):
            return wlp_seq(stmts, Q, depth + 1)

        case c0.Decl(typ, name, init):
            guard = divmod_guard(init) if init is not None else _true()
            default: c0.Exp = (
                (c0.ArrMake(_int(0)) if isinstance(typ, c0.ArrayType) else _int(0))
                if init is None else init
            )
            result = c0_util.subst_exp(Q, name, default)
            return _and(guard, result), []

        case c0.Assign(dest, src):
            guard = divmod_guard(src)
            result = c0_util.subst_exp(Q, dest, src)
            return _and(guard, result), []

        case c0.AllocArray(dest, typ, count):
            guard = divmod_guard(count)
            safe  = _and(guard, _le(_int(0), count))
            Q2    = c0_util.subst_exp(Q, dest, c0.ArrMake(count))
            return _and(safe, Q2), []

        case c0.ArrRead(dest, arr, idx):
            guard = divmod_guard(idx)
            safe  = _and(guard, _and(_le(_int(0), idx), _lt(idx, _len(arr))))
            Q2    = c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, idx))
            return _and(safe, Q2), []

        case c0.ArrWrite(arr, idx, val):
            guard = _and(divmod_guard(idx), divmod_guard(val))
            safe  = _and(guard, _and(_le(_int(0), idx), _lt(idx, _len(arr))))
            if isinstance(arr, c0.Var):
                new_arr = c0.ArrSet(arr, idx, val)
                Q2 = c0_util.subst_exp(Q, arr.name, new_arr)
                Q2 = _normalize_length(Q2)
            else:
                Q2 = Q
            return _and(safe, Q2), []

        case c0.If(cond, true_branch, false_branch):
            Q_true,  wb_true  = wlp(true_branch, Q, depth + 1)
            Q_false, wb_false = (wlp(false_branch, Q, depth + 1)
                                 if false_branch is not None else (Q, []))
            result = _and(
                divmod_guard(cond),
                _and(_implies(cond, Q_true), _implies(_not(cond), Q_false)),
            )
            return result, wb_true + wb_false

        case c0.While(cond, invs, body):
            return wlp_while(cond, invs, body, Q, depth)

        case c0.Assert(cond):
            return _and(divmod_guard(cond), _and(cond, Q)), []

        case c0.Error(_):
            # error() is always safe — continuation is irrelevant.
            return _true(), []

        case c0.Return(_):
            return Q, []

        case _:
            return Q, []


def wlp_seq(stmts: List[c0.Stmt], Q: c0.Exp, depth: int = 0) -> Tuple[c0.Exp, WhiteBox]:
    result = Q
    all_wb: WhiteBox = []
    for stmt in reversed(stmts):
        result, wb = wlp(stmt, result, depth)
        all_wb = wb + all_wb
    return result, all_wb


def wlp_while(
    cond: c0.Exp,
    invs: List[c0.Exp],
    body: c0.Stmt,
    Q: c0.Exp,
    depth: int = 0,
) -> Tuple[c0.Exp, WhiteBox]:

    if not invs:
        # No invariant supplied — cannot verify. Conservatively unsafe.
        return _false(), []

    # Combine multiple invariants into one conjunction.
    inv: c0.Exp = invs[0]
    for i in invs[1:]:
        inv = _and(inv, i)


    body_wlp, inner_wb = wlp(body, inv, depth + 1)
    modified = c0_util.get_defs(body)
    scalar_modified = {
        v for v in modified
        if v in _var_types and not isinstance(_var_types[v], c0.ArrayType)
    }
    all_vars = (
        c0_util.vars_exp(inv)
        | c0_util.vars_exp(cond)
        | c0_util.vars_exp(body_wlp)
        | c0_util.vars_exp(Q)
    )
    avoid = all_vars | c0_util.vars_stmt(body)
    scalar_vars = scalar_modified
    fresh_map: Dict[str, str] = {}
    for var in sorted(scalar_vars):
        fresh = c0_util.get_fresh_name(var + "_s", avoid)
        avoid.add(fresh)
        fresh_map[var] = fresh

    # Register fresh var types so the solver encodes them correctly
    fresh_types: Dict[str, c0.Type] = {}
    for orig, fresh in fresh_map.items():
        if orig in _var_types:
            fresh_types[fresh] = _var_types[orig]
    _register_types(fresh_types)

    # Substitute all vars to fresh states
    inv_sym = inv
    cond_sym = cond
    body_wlp_sym = body_wlp
    Q_sym = Q
    for orig, fresh in fresh_map.items():
        inv_sym = c0_util.subst_exp(inv_sym, orig, c0.Var(fresh))
        cond_sym = c0_util.subst_exp(cond_sym, orig, c0.Var(fresh))
        body_wlp_sym = c0_util.subst_exp(body_wlp_sym, orig, c0.Var(fresh))
        Q_sym = c0_util.subst_exp(Q_sym, orig, c0.Var(fresh))
    inv_sym = _normalize_length(inv_sym)
    body_wlp_sym = _normalize_length(body_wlp_sym)
    Q_sym = _normalize_length(Q_sym)

    cond_guard = divmod_guard(cond_sym)
    preservation_inner = _implies(
        _and(inv_sym, _and(cond_sym, cond_guard)), body_wlp_sym
    )
    exit_inner = _implies(
        _and(inv_sym, _and(_not(cond_sym), cond_guard)), Q_sym
    )

    fresh_vars = list(fresh_map.values())
    if fresh_vars:
        preservation = c0.ForAll(fresh_vars, preservation_inner)
        exit_condition = c0.ForAll(fresh_vars, exit_inner)
    else:
        preservation = preservation_inner
        exit_condition = exit_inner

    substituted_inner_wb = []
    for wb_formula in inner_wb:
        wb_sym = wb_formula
        for orig, fresh in fresh_map.items():
            wb_sym = c0_util.subst_exp(wb_sym, orig, c0.Var(fresh))
        substituted_inner_wb.append(_normalize_length(wb_sym))

    wrapped_inner_wb = []
    for wb_formula in substituted_inner_wb:
        if fresh_vars:
            guarded = _implies(inv_sym, wb_formula)
            wrapped_inner_wb.append(c0.ForAll(fresh_vars, guarded))
        else:
            wrapped_inner_wb.append(wb_formula)

    white_box_obligations = wrapped_inner_wb + [preservation, exit_condition]
    establishment = _and(divmod_guard(cond), inv)

    return establishment, white_box_obligations


# Top-level

def check_safety(prog: c0.Program) -> bool:
    """Check memory safety w/ WLP and white-box obligations."""
    global _var_types
    c0_util.clear_subst_caches()
    prog = c0_util.rename_program(prog)

    _var_types = collect_types(prog)
    solver.set_var_types(_var_types)

    pre: c0.Exp = _true()
    for req in (prog.requires or []):
        pre = _and(pre, req)

    post: c0.Exp = _true()
    for ens in (prog.ensures or []):
        post = _and(post, ens)

    stmts = prog.stmts
    if stmts and isinstance(stmts[-1], c0.Return):
        return_val = stmts[-1].val
        body_stmts = stmts[:-1]
    else:
        return_val = None
        body_stmts = stmts

    post_subst = (c0_util.subst_result(post, return_val)
                  if return_val is not None else post)

    formula, white_boxes = wlp_seq(body_stmts, post_subst)

    pre_simplified = c0_util.simplify(pre)

    for wb in white_boxes:
        wb_s = c0_util.simplify(_normalize_length(wb))
        try:
            if not solver.check_validity(wb_s):
                return False
        except Exception as exc:
            raise RuntimeError(
                f"[check_safety] Z3 ENCODING ERROR on white-box\n"
                f"  WB   : {c0_util.stringify(wb_s, pretty=True)}\n"
                f"  Error: {exc}"
            ) from exc

    vc = _implies(pre_simplified, c0_util.simplify(_normalize_length(formula)))
    try:
        if not solver.check_validity(vc):
            return False
        return True
    except Exception as exc:
        raise RuntimeError(
            f"[check_safety] Z3 ENCODING ERROR on main VC\n"
            f"  VC   : {c0_util.stringify(vc, pretty=True)}\n"
            f"  Error: {exc}"
        ) from exc