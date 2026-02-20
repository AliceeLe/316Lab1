"""Utilities for manipulating and printing C0 ASTs.

This module focuses on expression substitution and variable renaming. It uses
id-based caches because the AST dataclasses are unhashable, and WLP produces
very large formulas that would be expensive to traverse repeatedly.
"""

import c0
from typing import Set, Dict, List, Optional
import itertools
import functools

_SUBST_NODE_TABLE: Dict[int, c0.Exp] = {}

def _subst_reg(e: c0.Exp) -> int:
    """Register `e` in the node table and return its id (used as a cache key)."""
    eid = id(e)
    _SUBST_NODE_TABLE[eid] = e
    return eid

@functools.lru_cache(maxsize=200_000)
def _vars_exp_cached(eid: int) -> frozenset[str]:
    """Return the set of free variable names in the expression registered as `eid`."""
    e = _SUBST_NODE_TABLE[eid]
    match e:
        case c0.Var(name): return frozenset([name])
        case c0.IntConst(_) | c0.BoolConst(_) | c0.NullConst() | c0.ResultVar(): return frozenset()
        case c0.BinOp(_, l, r): return _vars_exp_cached(_subst_reg(l)) | _vars_exp_cached(_subst_reg(r))
        case c0.UnOp(_, arg): return _vars_exp_cached(_subst_reg(arg))
        case c0.Length(arg): return _vars_exp_cached(_subst_reg(arg))
        case c0.ArrayAccess(arr, idx): return _vars_exp_cached(_subst_reg(arr)) | _vars_exp_cached(_subst_reg(idx))
        case c0.ArrMake(length): return _vars_exp_cached(_subst_reg(length))
        case c0.ArrSet(arr, idx, val): return _vars_exp_cached(_subst_reg(arr)) | _vars_exp_cached(_subst_reg(idx)) | _vars_exp_cached(_subst_reg(val))
        case c0.ForAll(vars, body): return _vars_exp_cached(_subst_reg(body)) - frozenset(vars)
        case _: return frozenset()

@functools.lru_cache(maxsize=400_000)
def _subst_exp_cached(eid: int, x: str, rid: int) -> c0.Exp:
    """Substitute `x := replacement` into the expression registered as `eid` (capture-avoiding)."""
    e = _SUBST_NODE_TABLE[eid]
    replacement = _SUBST_NODE_TABLE[rid]
    match e:
        case c0.Var(name): return replacement if name == x else e
        case c0.IntConst(_) | c0.BoolConst(_) | c0.NullConst(): return e
        case c0.BinOp(op, l, r): return c0.BinOp(op, _subst_exp_cached(_subst_reg(l), x, rid), _subst_exp_cached(_subst_reg(r), x, rid))
        case c0.UnOp(op, arg): return c0.UnOp(op, _subst_exp_cached(_subst_reg(arg), x, rid))
        case c0.Length(arg): return c0.Length(_subst_exp_cached(_subst_reg(arg), x, rid))
        case c0.ArrayAccess(arr, idx): return c0.ArrayAccess(_subst_exp_cached(_subst_reg(arr), x, rid), _subst_exp_cached(_subst_reg(idx), x, rid))
        case c0.ResultVar(): return e
        case c0.ArrMake(length):
            return c0.ArrMake(_subst_exp_cached(_subst_reg(length), x, rid))
        case c0.ArrSet(arr, idx, val):
            return c0.ArrSet(
                _subst_exp_cached(_subst_reg(arr), x, rid),
                _subst_exp_cached(_subst_reg(idx), x, rid),
                _subst_exp_cached(_subst_reg(val), x, rid),
            )
        case c0.ForAll(bound_vars, body):
            if x in bound_vars: return e
            replacement_vars = _vars_exp_cached(rid)
            if not (set(bound_vars) & replacement_vars):
                return c0.ForAll(bound_vars, _subst_exp_cached(_subst_reg(body), x, rid))

            # Alpha-rename bound vars that would be captured by `replacement`.
            avoid = set(replacement_vars) | set(_vars_exp_cached(_subst_reg(body))) | set(bound_vars)
            new_vars = []
            current_body = body
            for bv in bound_vars:
                if bv in replacement_vars:
                    new_bv = get_fresh_name(bv, avoid)
                    avoid.add(new_bv)
                    new_vars.append(new_bv)
                    current_body = _subst_exp_cached(_subst_reg(current_body), bv, _subst_reg(c0.Var(new_bv)))
                else:
                    new_vars.append(bv)
            return c0.ForAll(new_vars, _subst_exp_cached(_subst_reg(current_body), x, rid))
        case _: return e

@functools.lru_cache(maxsize=200_000)
def _subst_result_cached(eid: int, rid: int) -> c0.Exp:
    """Substitute `\\result := replacement` into the expression registered as `eid`."""
    e = _SUBST_NODE_TABLE[eid]
    replacement = _SUBST_NODE_TABLE[rid]
    match e:
        case c0.ResultVar(): return replacement
        case c0.Var(_) | c0.IntConst(_) | c0.BoolConst(_) | c0.NullConst(): return e
        case c0.BinOp(op, l, r): return c0.BinOp(op, _subst_result_cached(_subst_reg(l), rid), _subst_result_cached(_subst_reg(r), rid))
        case c0.UnOp(op, arg): return c0.UnOp(op, _subst_result_cached(_subst_reg(arg), rid))
        case c0.Length(arg): return c0.Length(_subst_result_cached(_subst_reg(arg), rid))
        case c0.ArrayAccess(arr, idx): return c0.ArrayAccess(_subst_result_cached(_subst_reg(arr), rid), _subst_result_cached(_subst_reg(idx), rid))
        case c0.ArrMake(length):
            return c0.ArrMake(_subst_result_cached(_subst_reg(length), rid))
        case c0.ArrSet(arr, idx, val):
            return c0.ArrSet(
                _subst_result_cached(_subst_reg(arr), rid),
                _subst_result_cached(_subst_reg(idx), rid),
                _subst_result_cached(_subst_reg(val), rid),
            )
        case c0.ForAll(bound_vars, body): return c0.ForAll(bound_vars, _subst_result_cached(_subst_reg(body), rid))
        case _: return e

@functools.lru_cache(maxsize=200_000)
def _simplify_cached(eid: int) -> c0.Exp:
    """Perform small, local simplifications on the expression registered as `eid`."""
    e = _SUBST_NODE_TABLE[eid]
    match e:
        case c0.BinOp(op, l, r):
            sl = _simplify_cached(_subst_reg(l))
            sr = _simplify_cached(_subst_reg(r))
            if op == "&&":
                if isinstance(sl, c0.BoolConst) and sl.value: return sr
                if isinstance(sr, c0.BoolConst) and sr.value: return sl
            return c0.BinOp(op, sl, sr)
        case c0.UnOp(op, arg): return c0.UnOp(op, _simplify_cached(_subst_reg(arg)))
        case c0.Length(arg): return c0.Length(_simplify_cached(_subst_reg(arg)))
        case c0.ArrayAccess(arr, idx): return c0.ArrayAccess(_simplify_cached(_subst_reg(arr)), _simplify_cached(_subst_reg(idx)))
        case c0.ArrMake(length): return c0.ArrMake(_simplify_cached(_subst_reg(length)))
        case c0.ArrSet(arr, idx, val):
            return c0.ArrSet(_simplify_cached(_subst_reg(arr)), _simplify_cached(_subst_reg(idx)), _simplify_cached(_subst_reg(val)))
        case c0.ForAll(vars, body): return c0.ForAll(vars, _simplify_cached(_subst_reg(body)))
        case _: return e

@functools.lru_cache(maxsize=400_000)
def _stringify_cached(eid: int, indent: int, pretty: bool) -> str:
    """Render the expression registered as `eid` as a human-readable string."""
    e = _SUBST_NODE_TABLE[eid]
    space = "  " * indent
    next_space = "  " * (indent + 1)
    match e:
        case c0.Var(name): return name
        case c0.IntConst(v): return str(v)
        case c0.BoolConst(v): return "true" if v else "false"
        case c0.NullConst(): return "NULL"

        case c0.BinOp(op, l, r):
            if pretty and op in ["&&", "||", "=>"]:
                return f"({_stringify_cached(_subst_reg(l), indent + 1, pretty)} \n{next_space}{op} {_stringify_cached(_subst_reg(r), indent + 1, pretty)})"
            return f"({_stringify_cached(_subst_reg(l), indent, pretty)} {op} {_stringify_cached(_subst_reg(r), indent, pretty)})"

        case c0.UnOp(op, arg): return f"({op}{_stringify_cached(_subst_reg(arg), indent, pretty)})"
        case c0.Length(arg): return f"\\length({_stringify_cached(_subst_reg(arg), indent, pretty)})"
        case c0.ArrayAccess(arr, idx): return f"{_stringify_cached(_subst_reg(arr), indent, pretty)}[{_stringify_cached(_subst_reg(idx), indent, pretty)}]"
        case c0.ResultVar(): return "\\result"
        case c0.ArrMake(length):
            return f"ArrMake({_stringify_cached(_subst_reg(length), indent, pretty)})"
        case c0.ArrSet(arr, idx, val):
            return f"ArrSet({_stringify_cached(_subst_reg(arr), indent, pretty)}, {_stringify_cached(_subst_reg(idx), indent, pretty)}, {_stringify_cached(_subst_reg(val), indent, pretty)})"
        case c0.ForAll(vars, body):
            if pretty:
                return f"forall {', '.join(vars)} :: \n{next_space}{_stringify_cached(_subst_reg(body), indent + 1, pretty)}"
            return f"forall {','.join(vars)} :: {_stringify_cached(_subst_reg(body), indent, pretty)}"
        case _: return str(e)

def clear_subst_caches() -> None:
    """Clear all substitution/stringify caches (call once per verification run)."""
    _SUBST_NODE_TABLE.clear()
    _vars_exp_cached.cache_clear()
    _subst_exp_cached.cache_clear()
    _subst_result_cached.cache_clear()
    _simplify_cached.cache_clear()
    _stringify_cached.cache_clear()

def vars_exp(e: c0.Exp) -> set[str]:
    """Return the set of free variable names appearing in `e`."""
    return set(_vars_exp_cached(_subst_reg(e)))

def vars_stmt(s: c0.Stmt) -> set[str]:
    """Return the set of variable names appearing anywhere in statement `s`."""
    match s:
        case c0.Decl(_, name, init): return ({name} | vars_exp(init)) if init else {name}
        case c0.Assign(dest, src): return {dest} | vars_exp(src)
        case c0.AllocArray(dest, _, count): return {dest} | vars_exp(count)
        case c0.ArrRead(dest, arr, idx): return {dest} | vars_exp(arr) | vars_exp(idx)
        case c0.ArrWrite(arr, idx, val): return vars_exp(arr) | vars_exp(idx) | vars_exp(val)
        case c0.Block(stmts):
            v = set()
            for stmt in stmts: v |= vars_stmt(stmt)
            return v
        case c0.If(cond, t, f):
            return vars_exp(cond) | vars_stmt(t) | (vars_stmt(f) if f else set())
        case c0.While(cond, invs, body):
            v = vars_exp(cond) | vars_stmt(body)
            for i in invs: v |= vars_exp(i)
            return v
        case c0.Assert(cond): return vars_exp(cond)
        case c0.Error(_): return set()
        case c0.Return(val): return vars_exp(val) if val else set()
        case _: return set()

def simplify(e: c0.Exp) -> c0.Exp:
    """Return a simplified copy of expression `e` (cheap, local rewrites only)."""
    return _simplify_cached(_subst_reg(e))

def stringify(e: c0.Exp, indent: int = 0, pretty: bool = False) -> str:
    """Convert expression `e` to a string (use `pretty=True` for multi-line formatting)."""
    return _stringify_cached(_subst_reg(e), indent, pretty)

def stringify_stmt(s: c0.Stmt) -> str:
    """Convert statement `s` to a compact string (for debug output)."""
    match s:
        case c0.Decl(type, name, init):
             if init is None:
                 return f"{type} {name}"
             return f"{type} {name} = {stringify(init)}"
        case c0.Assign(dest, src): return f"{dest} = {stringify(src)}"
        case c0.AllocArray(dest, type, count): return f"{dest} = alloc_array({type}, {stringify(count)})"
        case c0.ArrRead(dest, arr, idx): return f"{dest} = {stringify(arr)}[{stringify(idx)}]"
        case c0.ArrWrite(arr, idx, val): return f"{stringify(arr)}[{stringify(idx)}] = {stringify(val)}"
        case c0.Block(stmts): return "Block {...}"
        case c0.If(cond, _, _): return f"if ({stringify(cond)}) ..."
        case c0.While(cond, _, _): return f"while ({stringify(cond)}) ..."
        case c0.Assert(cond): return f"assert({stringify(cond)})"
        case c0.Error(msg): return f"error({msg})"
        case c0.Return(val): return f"return {stringify(val) if val else ''}"
        case _: return str(s)

def get_fresh_name(base: str, avoid: set[str]) -> str:
    """Return a name based on `base` that is not present in `avoid`."""
    if base not in avoid: return base
    i = 0
    while True:
        candidate = f"{base}_{i}"
        if candidate not in avoid: return candidate
        i += 1

def subst_exp(e: c0.Exp, x: str, replacement: c0.Exp) -> c0.Exp:
    """Return `e` with all free occurrences of variable `x` replaced by `replacement`."""
    return _subst_exp_cached(_subst_reg(e), x, _subst_reg(replacement))

def subst_result(e: c0.Exp, replacement: c0.Exp) -> c0.Exp:
    """Return `e` with all occurrences of `\\result` replaced by `replacement`."""
    return _subst_result_cached(_subst_reg(e), _subst_reg(replacement))

def get_defs(s: c0.Stmt) -> set[str]:
    """Return variable names that may be defined/modified by executing `s`."""
    match s:
        case c0.Decl(_, name, _): return {name} 
        case c0.Assign(dest, _): return {dest}
        case c0.AllocArray(dest, _, _): return {dest}
        case c0.ArrRead(dest, _, _): return {dest}
        case c0.ArrWrite(arr, _, _):
            if isinstance(arr, c0.Var):
                return {arr.name}
            return set()
        case c0.Block(stmts):
            d = set()
            for stmt in stmts: d |= get_defs(stmt)
            return d
        case c0.If(_, t, f):
            return get_defs(t) | (get_defs(f) if f else set())
        case c0.While(_, _, body):
            return get_defs(body)
        case _: return set()

class Renamer:
    def __init__(self):
        """Create an alpha-renamer with an initial empty scope stack."""
        self.scopes: List[Dict[str, str]] = [{}]
        self.counter = 0

    def fresh(self, base: str) -> str:
        """Return a fresh unique name based on `base` (used for alpha-renaming)."""
        self.counter += 1
        return f"{base}_{self.counter}"

    def current(self, name: str) -> str:
        """Return the current renamed version of `name` (or `name` if unbound)."""
        for scope in reversed(self.scopes):
            if name in scope: return scope[name]
        return name 
    
    def enter_scope(self):
        """Push a new lexical scope for renaming."""
        self.scopes.append({})
    
    def exit_scope(self):
        """Pop the most recent lexical scope for renaming."""
        self.scopes.pop()
    
    def declare(self, name: str) -> str:
        """Declare a new binding for `name` in the current scope and return its fresh name."""
        new_name = self.fresh(name)
        self.scopes[-1][name] = new_name
        return new_name

    def rename_exp(self, e: c0.Exp) -> c0.Exp:
        """Alpha-rename all variable occurrences inside expression `e`."""
        match e:
            case c0.Var(name): return c0.Var(self.current(name))
            case c0.BinOp(op, l, r): return c0.BinOp(op, self.rename_exp(l), self.rename_exp(r))
            case c0.UnOp(op, arg): return c0.UnOp(op, self.rename_exp(arg))
            case c0.Length(arg): return c0.Length(self.rename_exp(arg))
            case c0.ArrayAccess(arr, idx): return c0.ArrayAccess(self.rename_exp(arr), self.rename_exp(idx))
            case c0.ArrMake(length): return c0.ArrMake(self.rename_exp(length))
            case c0.ArrSet(arr, idx, val): return c0.ArrSet(self.rename_exp(arr), self.rename_exp(idx), self.rename_exp(val))
            case c0.ResultVar(): return c0.ResultVar()
            case c0.ForAll(vars, body): 
                return c0.ForAll(vars, self.rename_exp(body))
            case _: return e

    def rename_stmt(self, s: c0.Stmt) -> c0.Stmt:
        """Alpha-rename all variable occurrences inside statement `s`."""
        match s:
            case c0.Decl(t, name, init):
                # Init is evaluated in current scope
                r_init = self.rename_exp(init) if init else None
                # Then declare name
                new_name = self.declare(name)
                return c0.Decl(t, new_name, r_init)
            
            case c0.Assign(dest, src):
                return c0.Assign(self.current(dest), self.rename_exp(src))
            
            case c0.AllocArray(dest, type, count):
                return c0.AllocArray(self.current(dest), type, self.rename_exp(count))
            
            case c0.ArrRead(dest, arr, idx):
                return c0.ArrRead(self.current(dest), self.rename_exp(arr), self.rename_exp(idx))
            
            case c0.ArrWrite(arr, idx, val):
                return c0.ArrWrite(self.rename_exp(arr), self.rename_exp(idx), self.rename_exp(val))
            
            case c0.Block(stmts):
                self.enter_scope()
                r_stmts = [self.rename_stmt(stmt) for stmt in stmts]
                self.exit_scope()
                return c0.Block(r_stmts)
            
            case c0.If(cond, t, f):
                r_cond = self.rename_exp(cond)
                
                self.enter_scope()
                r_t = self.rename_stmt(t)
                self.exit_scope()
                
                r_f = None
                if f:
                    self.enter_scope()
                    r_f = self.rename_stmt(f)
                    self.exit_scope()
                return c0.If(r_cond, r_t, r_f)
            
            case c0.While(cond, invs, body):
                r_cond = self.rename_exp(cond)
                r_invs = [self.rename_exp(i) for i in invs]
                
                self.enter_scope()
                r_body = self.rename_stmt(body)
                self.exit_scope()
                return c0.While(r_cond, r_invs, r_body)
            
            case c0.Assert(cond):
                return c0.Assert(self.rename_exp(cond))
            
            case c0.Return(val):
                 return c0.Return(self.rename_exp(val) if val else None)
            
            case _: return s

def rename_program(prog: c0.Program) -> c0.Program:
    """Return an alpha-renamed copy of `prog` where shadowing cannot occur."""
    r = Renamer()
    r.enter_scope() # Global scope? Or func scope?
    
    # Declare args first
    new_args = []
    if prog.args:
        for arg in prog.args:
            new_args.append(r.declare(arg))

    # Rename requires
    new_reqs = []
    if prog.requires:
        new_reqs = [r.rename_exp(e) for e in prog.requires]

    # Rename statements
    new_stmts = [r.rename_stmt(s) for s in prog.stmts]
    
    # Rename ensures
    new_ens = []
    if prog.ensures:
        new_ens = [r.rename_exp(e) for e in prog.ensures]
    
    r.exit_scope()
    return c0.Program(new_stmts, requires=new_reqs, ensures=new_ens, args=new_args)
