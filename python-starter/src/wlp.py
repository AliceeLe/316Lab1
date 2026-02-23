"""WLP-based memory safety checker.

Per the lecture notes (Lecture 7, Section 8), the WLP for a while loop
produces three components:
  1. Establishment  : J          (inline, checked with precondition)
  2. □(J ∧ cond → wlp body J)   (white-box: checked standalone, universally)
  3. □(J ∧ ¬cond → Q)           (white-box: checked standalone, universally)

White-box formulas are "pulled out" and checked independently for validity.
They are NOT folded into the main implication P → wlp α Q, because the □
modality erases all context — they must be valid in every state.
"""

from __future__ import annotations

from typing import List, Dict, Tuple

import c0
import c0_util
import solver

# ---------------------------------------------------------------------------
# Expression helpers
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Division/modulo safety guard
# ---------------------------------------------------------------------------

def divmod_guard(e: c0.Exp) -> c0.Exp:
    """Conjoin denominator != 0 for every / and % in e (and in all subexpressions)."""
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


# ---------------------------------------------------------------------------
# Module-level type environment
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# WLP  — returns (formula, white_box_obligations)
#
# white_box_obligations is a list of formulas that must each be checked
# independently for validity (they correspond to □P in the lecture notes).
# ---------------------------------------------------------------------------

WhiteBox = List[c0.Exp]  # type alias


def wlp(stmt: c0.Stmt, Q: c0.Exp, depth: int = 0) -> Tuple[c0.Exp, WhiteBox]:
    """
    Return (wlp(stmt, Q), white_box_obligations).

    The white-box obligations are formulas that must be valid in every state
    (the □ formulas from the while rule). They are checked separately in
    check_safety, not folded into the main implication.
    """
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
            safe = _le(_int(0), count)
            Q2   = c0_util.subst_exp(Q, dest, c0.ArrMake(count))
            return _and(safe, Q2), []

        case c0.ArrRead(dest, arr, idx):
            safe = _and(_le(_int(0), idx), _lt(idx, _len(arr)))
            Q2   = c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, idx))
            return _and(safe, Q2), []

        case c0.ArrWrite(arr, idx, val):
            safe = _and(_le(_int(0), idx), _lt(idx, _len(arr)))
            if isinstance(arr, c0.Var):
                Q2 = c0_util.subst_exp(Q, arr.name, c0.ArrSet(arr, idx, val))
            else:
                Q2 = Q
            return _and(safe, Q2), []

        case c0.If(cond, true_branch, false_branch):
            Q_true,  wb_true  = wlp(true_branch, Q, depth + 1)
            Q_false, wb_false = (wlp(false_branch, Q, depth + 1)
                                 if false_branch is not None else (Q, []))
            result = _and(_implies(cond, Q_true), _implies(_not(cond), Q_false))
            return result, wb_true + wb_false

        case c0.While(cond, invs, body):
            return wlp_while(cond, invs, body, Q, depth)

        case c0.Assert(cond):
            return _and(cond, Q), []

        case c0.Error(_):
            # error() is always safe — continuation is irrelevant.
            return _true(), []

        case c0.Return(_):
            return Q, []

        case _:
            return Q, []


def wlp_seq(stmts: List[c0.Stmt], Q: c0.Exp, depth: int = 0) -> Tuple[c0.Exp, WhiteBox]:
    """WLP of a statement sequence — fold right, accumulating white-box obligations."""
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
    """
    WLP of a while loop with invariants, following Lecture 7 Section 6 & 8.

    wlp(while^J cond body) Q =
        J                              ← establishment (inline, uses concrete pre-loop values)
      ∧ □(J ∧ cond  → wlp body J)    ← preservation  (white-box: checked standalone)
      ∧ □(J ∧ ¬cond → Q)             ← exit           (white-box: checked standalone)

    The □ formulas are returned as white-box obligations and checked
    independently for validity (with no surrounding context/precondition).
    """
    if not invs:
        # No invariant supplied — cannot verify. Conservatively unsafe.
        return _false(), []

    # Combine multiple invariants into one conjunction.
    inv: c0.Exp = invs[0]
    for i in invs[1:]:
        inv = _and(inv, i)

    # ------------------------------------------------------------------
    # Build the preservation white-box:  □(J ∧ cond → wlp(body, J))
    #
    # wlp(body, J) uses fresh symbolic variables for every scalar variable
    # modified by the body, so the white-box is checked universally over
    # all states satisfying J — not just the concrete pre-loop state.
    #
    # Array-typed modified vars are NOT given fresh names because
    # solver.py's ForAll encoder only handles BitVec-sorted variables.
    # Instead they remain as free uninterpreted constants whose lengths
    # are constrained by the invariant (e.g. \length(arr) == argc).
    # ------------------------------------------------------------------
    modified = c0_util.get_defs(body)

    avoid = (
        c0_util.vars_exp(inv)
        | c0_util.vars_exp(cond)
        | c0_util.vars_stmt(body)
        | c0_util.vars_exp(Q)
    )
    fresh_map: Dict[str, str] = {}
    for var in sorted(modified):
        fresh = c0_util.get_fresh_name(var + "_s", avoid)
        avoid.add(fresh)
        fresh_map[var] = fresh

    # Register fresh var types so the solver encodes them correctly.
    fresh_types: Dict[str, c0.Type] = {}
    for orig, fresh in fresh_map.items():
        if orig in _var_types:
            fresh_types[fresh] = _var_types[orig]
    _register_types(fresh_types)

    # Substitute scalar modified vars → fresh in inv and cond.
    inv_sym  = inv
    cond_sym = cond
    for orig, fresh in fresh_map.items():
        inv_sym  = c0_util.subst_exp(inv_sym,  orig, c0.Var(fresh))
        cond_sym = c0_util.subst_exp(cond_sym, orig, c0.Var(fresh))

    # Compute wlp(body, inv_sym).
    # The body writes to original var names; backwards substitution replaces
    # them with expressions over fresh vars. Also collect any nested
    # white-box obligations from inside the body.
    body_wlp, inner_wb = wlp(body, inv, depth + 1)

    # Substitute any remaining original modified vars → fresh in body_wlp and Q.
    body_wlp_sym = body_wlp
    Q_sym = Q
    for orig, fresh in fresh_map.items():
        body_wlp_sym = c0_util.subst_exp(body_wlp_sym, orig, c0.Var(fresh))
        Q_sym        = c0_util.subst_exp(Q_sym,        orig, c0.Var(fresh))

    # Build the inner formulas for the two white-box obligations.
    preservation_inner = _implies(_and(inv_sym, cond_sym),       body_wlp_sym)
    exit_inner         = _implies(_and(inv_sym, _not(cond_sym)), Q_sym)

    # Universally quantify over fresh scalar vars (the □ modality).
    fresh_vars = list(fresh_map.values())
    if fresh_vars:
        preservation   = c0.ForAll(fresh_vars, preservation_inner)
        exit_condition = c0.ForAll(fresh_vars, exit_inner)
    else:
        preservation   = preservation_inner
        exit_condition = exit_inner

    # Per Section 8: the white-box formulas are pulled out and checked
    # separately. The inline result is just the establishment J.
    white_box_obligations = inner_wb + [preservation, exit_condition]

    return inv, white_box_obligations


# ---------------------------------------------------------------------------
# Top-level
# ---------------------------------------------------------------------------

def check_safety(prog: c0.Program) -> bool:
    """
    Check memory safety via WLP + white-box obligations.

    Per Lecture 7 Section 8:
      - Compute (formula, white_boxes) = wlp(body, post)
      - Check each white_box is independently valid (no precondition context)
      - Check valid(pre → formula) for the main VC
    All must pass for the program to be safe.
    """
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

    import sys
    print(f"[WLP DEBUG] {len(white_boxes)} white-box obligations", file=sys.stderr)
    
    # Check all white-box obligations first (standalone, no precondition).
    # These correspond to □P formulas from the while rule — they must be
    # valid in every state, so we check them with no surrounding context.
    for idx, wb in enumerate(white_boxes):
        wb_simplified = c0_util.simplify(wb)
        try:
            wb_valid = solver.check_validity(wb_simplified)
            if not wb_valid:
                return False
        except Exception as exc:
            raise RuntimeError(
                f"[check_safety] Z3 ENCODING ERROR on white-box\n"
                f"  WB   : {c0_util.stringify(wb_simplified, pretty=True)}\n"
                f"  Error: {exc}"
            ) from exc

    # Check the main VC: pre → wlp(body, post).
    vc = _implies(c0_util.simplify(pre), c0_util.simplify(formula))
    try:
        return solver.check_validity(vc)
    except Exception as exc:
        raise RuntimeError(
            f"[check_safety] Z3 ENCODING ERROR on main VC\n"
            f"  VC   : {c0_util.stringify(vc, pretty=True)}\n"
            f"  Error: {exc}"
        ) from exc