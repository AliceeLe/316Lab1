"""Encode verification conditions into Z3 and discharge them.

This module provides:
- An encoding from `c0.py` expressions into Z3, and
- Helpers to extract and pretty-print counterexample models.
"""

import c0
from typing import Optional
import z3
from dataclasses import dataclass

BIT_WIDTH = 64

IntSort = z3.BitVecSort(BIT_WIDTH)
ValSort = z3.BitVecSort(BIT_WIDTH)
ArrDataSort = z3.ArraySort(IntSort, ValSort)  # Index(BV) -> Val(BV)

_ARR_OBJ_SORT: Optional[z3.DatatypeSortRef] = None
_VAR_TYPES: dict[str, c0.Type] = {}


def _arr_sort() -> z3.DatatypeSortRef:
    """Return the Z3 datatype sort used to represent `int[]` values."""
    global _ARR_OBJ_SORT
    if _ARR_OBJ_SORT is None:
        Arr = z3.Datatype("Arr")
        Arr.declare("mk", ("len", IntSort), ("data", ArrDataSort))
        _ARR_OBJ_SORT = Arr.create()
    return _ARR_OBJ_SORT


def set_var_types(var_types: dict[str, c0.Type]) -> None:
    """Install a type environment for encoding `Var(name)` with the right Z3 sort."""
    global _VAR_TYPES
    _VAR_TYPES = dict(var_types)

def simplify(func):
    """Decorate `func` to Z3-simplify any returned `z3.ExprRef`."""
    def simplifyInner(*args, **kwargs):
        """Call `func` and simplify its Z3 result (if any)."""
        ret = func(*args, **kwargs)
        if isinstance(ret, (z3.ExprRef)):
            return z3.simplify(ret)
        return ret
    return simplifyInner

def get_z3_var(name: str) -> z3.ExprRef:
    """Return a Z3 variable for a C0 variable name (using the installed type env)."""
    t = _VAR_TYPES.get(name)
    if isinstance(t, c0.BoolType):
        return z3.Bool(name)
    if isinstance(t, c0.ArrayType):
        return z3.Const(name, _arr_sort())
    return z3.BitVec(name, BIT_WIDTH)


@simplify
def exp_enc(e: c0.Exp) -> z3.ExprRef:
    """Encode a `c0.py` expression as a Z3 expression."""
    Arr = _arr_sort()
    match e:
        case c0.IntConst(val):
            return z3.BitVecVal(val, BIT_WIDTH)
        case c0.BoolConst(val):
            return z3.BoolVal(val)
        case c0.NullConst():
            # NULL is rejected by the parser; keep a harmless encoding for robustness.
            return z3.BitVecVal(0, BIT_WIDTH)
        case c0.Var(name):
            return get_z3_var(name)

        case c0.BinOp(op, l, r):
            el = exp_enc(l)
            er = exp_enc(r)

            # Equality works for any same-sorted Z3 expressions (including arrays and datatypes).
            if op == "==":
                return el == er
            if op == "!=":
                return el != er

            if z3.is_bv(el) and z3.is_bv(er):
                match op:
                    case "+":
                        return el + er
                    case "-":
                        return el - er
                    case "*":
                        return el * er
                    case "/":
                        return el / er
                    case "%":
                        return z3.SRem(el, er)

                    case "<":
                        return el < er
                    case "<=":
                        return el <= er
                    case ">":
                        return el > er
                    case ">=":
                        return el >= er
                    case _:
                        raise ValueError(f"Unknown int op {op}")

            if z3.is_bool(el) and z3.is_bool(er):
                match op:
                    case "&&":
                        return z3.And(el, er)
                    case "||":
                        return z3.Or(el, er)
                    case "=>":
                        return z3.Implies(el, er)
                    case _:
                        raise ValueError(f"Unknown bool op {op}")

            raise ValueError(f"Unknown op {op} for Z3 sorts {el.sort()} and {er.sort()}")

        case c0.UnOp(op, arg):
            ea = exp_enc(arg)
            match op:
                case "!":
                    return z3.Not(ea)
                case "-":
                    return -ea
                case _:
                    raise ValueError(f"Unknown unop {op}")

        case c0.Length(arg):
            a = exp_enc(arg)
            if a.sort() != Arr:
                raise ValueError("\\length expects an int[] value")
            return Arr.len(a)

        case c0.ArrayAccess(arr, idx):
            a = exp_enc(arr)
            if a.sort() != Arr:
                raise ValueError("array indexing expects an int[] value")
            i = exp_enc(idx)
            return z3.Select(Arr.data(a), i)

        case c0.ArrMake(length):
            zlen = exp_enc(length)
            zdata = z3.Const(f"_arrmake_{id(e)}", ArrDataSort)
            return Arr.mk(zlen, zdata)

        case c0.ArrSet(arr, idx, val):
            a = exp_enc(arr)
            if a.sort() != Arr:
                raise ValueError("ArrSet expects an int[] value")
            i = exp_enc(idx)
            v = exp_enc(val)
            return Arr.mk(Arr.len(a), z3.Store(Arr.data(a), i, v))

        case c0.ForAll(vars, body):
            zvars = [z3.BitVec(v, BIT_WIDTH) for v in vars]
            return z3.ForAll(zvars, exp_enc(body))

        case _:
            raise TypeError(f"exp_enc got {type(e)}: {e}")

fmla_enc = exp_enc

def check_validity(f: c0.Exp) -> bool:
    """Return `True` iff formula `f` is valid (i.e. its negation is UNSAT)."""
    s = get_solver()
    zf = fmla_enc(f)
    # Simplify the VC before solving!
    vc = z3.simplify(z3.Not(zf))
    s.add(vc)
    res = s.check()
    return res == z3.unsat

def get_simplified_vc(f: c0.Exp) -> z3.ExprRef:
    """Return the *negated* VC `Not(enc(f))`, simplified for solving."""
    zf = fmla_enc(f)
    return z3.simplify(z3.Not(zf))

def get_solver() -> z3.Solver:
    """Create a Z3 solver configured with tactics tuned for this BitVec+Array workload."""
    t = z3.Tactic("smt")
    return t.solver()

def solve_vc(vc: z3.ExprRef) -> tuple[str, Optional[z3.ModelRef]]:
    """Solve a (negated) VC and return `(status, model)` where status is `valid|unsafe|unknown`."""
    s = get_solver()
    s.add(vc)
    res = s.check()
    if res == z3.unsat:
        return "valid", None
    elif res == z3.sat:
        return "unsafe", s.model()
    else:
        return "unknown", None

def _occurs_uninterpreted_name(expr: z3.ExprRef, name: str) -> bool:
    """Return `True` iff `name` appears as an uninterpreted constant in `expr`."""
    seen = set()
    stack = [expr]
    while stack:
        n = stack.pop()
        nid = n.get_id()
        if nid in seen:
            continue
        seen.add(nid)
        if z3.is_const(n) and n.decl().kind() == z3.Z3_OP_UNINTERPRETED and n.decl().name() == name:
            return True
        stack.extend(n.children())
    return False


@dataclass(frozen=True)
class ModelResult:
    status: str  # "valid" | "unsafe" | "unknown"
    model: Optional[z3.ModelRef]
    minimized: Optional[dict[str, int]] = None


def get_model(
    vc: z3.ExprRef,
    *,
    argc_name: Optional[str] = None,
    prefer_small_cex: bool = False,
    small_cex_max: int = 32,
) -> ModelResult:
    """
    Solve a (negated) VC and, if SAT, return a model.

    If `prefer_small_cex` is enabled and `argc_name` is provided, tries to find a
    smaller counterexample by constraining argc to 0..small_cex_max and returning
    the first satisfying model.
    """
    s = get_solver()
    s.add(vc)
    res = s.check()
    if res == z3.unsat:
        return ModelResult("valid", None, None)
    if res != z3.sat:
        return ModelResult("unknown", None, None)

    base_model = s.model()

    if not prefer_small_cex:
        return ModelResult("unsafe", base_model, None)
    if argc_name is None or small_cex_max < 0:
        return ModelResult("unsafe", base_model, None)
    if not _occurs_uninterpreted_name(vc, argc_name):
        return ModelResult("unsafe", base_model, None)

    z_argc = get_z3_var(argc_name)
    for k in range(0, small_cex_max + 1):
        s.push()
        s.add(z_argc == z3.BitVecVal(k, BIT_WIDTH))
        r = s.check()
        if r == z3.sat:
            return ModelResult("unsafe", s.model(), {"argc": k})
        s.pop()

    return ModelResult("unsafe", base_model, None)
