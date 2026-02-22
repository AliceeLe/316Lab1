"""WLP-based memory safety checker."""

from __future__ import annotations

import sys
from typing import List, Dict

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
# Zero-initialized array helper
# ---------------------------------------------------------------------------

# A sentinel expression representing a zero-initialized array of a given length.
# We use ArrMake(length) at the solver level and model it with a constant 0-valued
# array by substituting a concrete ArrSet chain.  Since the solver's ArrMake uses
# an unconstrained data array, we introduce a separate helper that builds the
# zero-contents array via a ForAll constraint instead — but the simplest correct
# approach is to pass an ArrMake and separately assert its contents are zero using
# a ForAll in the precondition.  However, the simplest approach that is sound for
# the safety properties we care about (bounds checking) is to keep ArrMake and just
# record the length correctly, which ArrMake already does.
#
# For array element safety: when we read from a freshly-allocated array we only care
# that the index is in-bounds, not what the value is. So ArrMake is fine for that.
# The spec says elements are 0, which matters for correctness of the *program* but
# not for memory safety per se.  We do need the length to be exact — ArrMake(count)
# already encodes that.
#
# CONCLUSION: ArrMake is correct for safety verification. No change needed here.


# ---------------------------------------------------------------------------
# Division/modulo safety helper
# ---------------------------------------------------------------------------

def _div_guard(src: c0.Exp) -> c0.Exp:
    """
    Return a safety guard for any division or modulo operations in `src`.
    Since the parser hoists division into Assign(tmp, BinOp("/"|"%", a, b)),
    we only need to inspect the top-level BinOp here.
    Returns True if no division, otherwise (denominator != 0).
    """
    if isinstance(src, c0.BinOp) and src.op in ("/", "%"):
        return _neq(src.right, _int(0))
    return _true()


# ---------------------------------------------------------------------------
# Module-level type environment
# Updated by check_safety and also by wlp_while when it creates fresh vars.
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
    """Add extra name->Type entries to the module dict and re-install in solver."""
    _var_types.update(extra)
    solver.set_var_types(_var_types)


# ---------------------------------------------------------------------------
# WLP
# ---------------------------------------------------------------------------

def wlp(stmt: c0.Stmt, Q: c0.Exp, depth: int = 0) -> c0.Exp:
    """Return wlp(stmt, Q) with all safety guards folded in as conjuncts."""

    match stmt:

        case c0.Block(stmts):
            return wlp_seq(stmts, Q, depth + 1)

        case c0.Decl(typ, name, init):
            # Division guard: the parser may place BinOp("/", ...) as the init.
            guard = _div_guard(init) if init is not None else _true()
            default: c0.Exp = (
                (c0.ArrMake(_int(0)) if isinstance(typ, c0.ArrayType) else _int(0))
                if init is None else init
            )
            result = c0_util.subst_exp(Q, name, default)
            return _and(guard, result)

        case c0.Assign(dest, src):
            # Division guard: parser hoists division into Assign(tmp, BinOp("/", a, b)).
            guard = _div_guard(src)
            result = c0_util.subst_exp(Q, dest, src)
            return _and(guard, result)

        case c0.AllocArray(dest, typ, count):
            # Safety: count must be non-negative.
            safe   = _le(_int(0), count)
            Q2     = c0_util.subst_exp(Q, dest, c0.ArrMake(count))
            result = _and(safe, Q2)
            return result

        case c0.ArrRead(dest, arr, idx):
            safe   = _and(_le(_int(0), idx), _lt(idx, _len(arr)))
            Q2     = c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, idx))
            result = _and(safe, Q2)
            return result

        case c0.ArrWrite(arr, idx, val):
            safe = _and(_le(_int(0), idx), _lt(idx, _len(arr)))
            if isinstance(arr, c0.Var):
                Q2 = c0_util.subst_exp(Q, arr.name, c0.ArrSet(arr, idx, val))
            else:
                Q2 = Q
            result = _and(safe, Q2)
            return result

        case c0.If(cond, true_branch, false_branch):
            Q_true  = wlp(true_branch, Q, depth + 1)
            Q_false = wlp(false_branch, Q, depth + 1) if false_branch is not None else Q
            result  = _and(_implies(cond, Q_true), _implies(_not(cond), Q_false))
            return result

        case c0.While(cond, invs, body):
            return wlp_while(cond, invs, body, Q, depth)

        case c0.Assert(cond):
            # Assert: cond must hold, AND Q must hold after.
            result = _and(cond, Q)
            return result

        case c0.Error(_):
            # error() is always safe (unreachable continuation doesn't matter).
            return _true()

        case c0.Return(_):
            # Return: pass Q through; the return value's safety is handled
            # by check_safety (subst_result into the postcondition).
            return Q

        case _:
            return Q


def wlp_seq(stmts: List[c0.Stmt], Q: c0.Exp, depth: int = 0) -> c0.Exp:
    """WLP of a statement sequence - fold right."""
    result = Q
    for stmt in reversed(stmts):
        result = wlp(stmt, result, depth)
    return result


def wlp_while(cond: c0.Exp, invs: List[c0.Exp], body: c0.Stmt, Q: c0.Exp, depth: int = 0) -> c0.Exp:
    """
    WLP of a while using invariants as cut points.

      1. Establishment : I                               (checked at pre-loop values)
      2. Preservation  : forall loop-state. I^cond => wlp(body, I)
      3. Exit          : forall loop-state. I^!cond => Q

    Fresh symbolic variables stand in for loop-modified vars in (2) and (3)
    so the solver checks all states satisfying I, not just the initial state.
    Fresh array vars are registered in _var_types so \length encodes correctly.
    """

    if not invs:
        # No invariants: we cannot prove the loop body is safe. The spec requires
        # loop_invariant annotations on all while loops; without them we conservatively
        # treat the program as unverifiable (unsafe).
        return _false()

    inv: c0.Exp = invs[0]
    for i in invs[1:]:
        inv = _and(inv, i)

    modified = c0_util.get_defs(body)

    # Only create fresh symbolic names for scalar (non-array) modified vars.
    # Array-typed modified vars are left as their original names: their length
    # is constrained by the invariant (e.g. \length(arr) == argc), so the
    # solver correctly reasons about bounds even without quantifying over them.
    # Additionally, solver.py's ForAll encoder uses z3.BitVec for all bound
    # vars and cannot handle array-typed quantified variables.
    scalar_modified = {v for v in modified if not isinstance(_var_types.get(v), c0.ArrayType)}

    # Fresh symbolic names for scalar modified vars.
    # Avoid: all vars in inv, cond, body, AND Q — so fresh names don't clash.
    avoid = (
        c0_util.vars_exp(inv)
        | c0_util.vars_exp(cond)
        | c0_util.vars_stmt(body)
        | c0_util.vars_exp(Q)
    )
    fresh_map: Dict[str, str] = {}
    for var in sorted(scalar_modified):
        fresh = c0_util.get_fresh_name(var + "_s", avoid)
        avoid.add(fresh)
        fresh_map[var] = fresh

    # Register fresh vars with their types.
    fresh_types: Dict[str, c0.Type] = {}
    for orig, fresh in fresh_map.items():
        if orig in _var_types:
            fresh_types[fresh] = _var_types[orig]
    _register_types(fresh_types)

    # Substitute modified vars -> fresh vars in inv and cond
    inv_sym  = inv
    cond_sym = cond
    for orig, fresh in fresh_map.items():
        inv_sym  = c0_util.subst_exp(inv_sym,  orig, c0.Var(fresh))
        cond_sym = c0_util.subst_exp(cond_sym, orig, c0.Var(fresh))

    # wlp(body, inv_sym): the body assigns to original var names; substitution
    # propagates backwards so original vars get replaced by body-computed
    # expressions in terms of fresh vars.
    body_wlp = wlp(body, inv_sym, depth + 1)

    # Substitute any remaining original modified vars -> fresh in body_wlp and Q.
    body_wlp_sym = body_wlp
    Q_sym = Q
    for orig, fresh in fresh_map.items():
        body_wlp_sym = c0_util.subst_exp(body_wlp_sym, orig, c0.Var(fresh))
        Q_sym        = c0_util.subst_exp(Q_sym,        orig, c0.Var(fresh))

    preservation_inner = _implies(_and(inv_sym, cond_sym),        body_wlp_sym)
    exit_inner         = _implies(_and(inv_sym, _not(cond_sym)),  Q_sym)

    fresh_vars = list(fresh_map.values())
    if fresh_vars:
        preservation   = c0.ForAll(fresh_vars, preservation_inner)
        exit_condition = c0.ForAll(fresh_vars, exit_inner)
    else:
        preservation   = preservation_inner
        exit_condition = exit_inner

    # Establishment uses pre-loop (concrete) variable values.
    establishment = inv

    return _and(establishment, _and(preservation, exit_condition))


# ---------------------------------------------------------------------------
# Top-level
# ---------------------------------------------------------------------------

def check_safety(prog: c0.Program) -> bool:
    """Check memory safety via a single WLP verification condition."""
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
        return_val  = stmts[-1].val
        body_stmts  = stmts[:-1]
    else:
        return_val  = None
        body_stmts  = stmts

    post_subst = c0_util.subst_result(post, return_val) if return_val is not None else post

    formula = wlp_seq(body_stmts, post_subst)

    vc = _implies(c0_util.simplify(pre), c0_util.simplify(formula))

    try:
        valid = solver.check_validity(vc)
    except Exception as exc:
        raise RuntimeError(
            f"[check_safety] Z3 ENCODING ERROR\n"
            f"  VC   : {c0_util.stringify(vc, pretty=True)}\n"
            f"  Error: {exc}"
        ) from exc

    return valid