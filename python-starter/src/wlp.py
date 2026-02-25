"""WLP-based memory safety checker (students implement)."""

from __future__ import annotations

import c0
import c0_util
import solver

#nts safety using wlp by proving p -> [alpha]Q holds
#to do this: compute wlp alpha Q and check if P -> wlp alpha Q & the 
#white box reqs


#ALL PRE LOGIC STUFF (ex; helpers & type checking to use solver.py helpers)
#helpers for expression symbols

def true_sym():  
    return c0.BoolConst(True)
def and_sym(a, b):
    if (isinstance(a, c0.BoolConst) and a.value):     
        return b
    if (isinstance(b, c0.BoolConst) and b.value):     
        return a
    if (isinstance(a, c0.BoolConst) and not a.value): 
        return a
    if (isinstance(b, c0.BoolConst) and not b.value): 
        return b
    return c0.BinOp("&&", a, b)
def not_sym(a):        
    return c0.UnOp("!", a)
def implies_sym(a, b): 
    return c0.BinOp("=>", a, b)
def leq(a, b):      
    return c0.BinOp("<=", a, b)
def int_sym(v):        
    return c0.IntConst(v)

#requires all denominator to be non zero
def denominator_zero_check(e):
    match e:
        #!= 0 for / and %
        case c0.BinOp(op, l, r):
            g = and_sym(denominator_zero_check(l), denominator_zero_check(r))
            if op in ("/", "%"):
                g = and_sym(g, c0.BinOp("!=", r, int_sym(0)))
            return g
            
        #recursively check every denominator in argument
        #to any of the following helper functions != 0 from 
        # c0.py. Ensures everytime we call one of those helpers it's safe

        case c0.UnOp(_, arg):           
            return denominator_zero_check(arg)
        case c0.ArrayAccess(arr, idx):  
            return and_sym(denominator_zero_check(arr), denominator_zero_check(idx))
        case c0.Length(arg):            
            return denominator_zero_check(arg)
        case c0.ArrMake(n):             
            return denominator_zero_check(n)
        case c0.ArrSet(arr, idx, val):  
            return and_sym(denominator_zero_check(arr), and_sym(denominator_zero_check(idx), denominator_zero_check(val)))
        case c0.ForAll(_, body):        
            return denominator_zero_check(body)
        #Base case ; everything's satisfied !!
        case _:                         
            return true_sym()


#need to map variables to c0 types to be usable by 
#solver.py when converting to z3 formulas. 
#type info stored in ast so need to read from this 
# by traversing the tree

def traverse_ast_types(s, types):
    match s:
        case c0.Decl(typ, name, _):
            types[name] = typ
        case c0.AllocArray(dest, typ, _):
            types[dest] = c0.ArrayType(typ)
        case c0.ArrRead(dest, _, _):
            types[dest] = c0.IntType()
        case c0.Block(commandList):
            for st in commandList:
                traverse_ast_types(st, types)
        case c0.If(_, t, f):
            traverse_ast_types(t, types)
            if f:
                traverse_ast_types(f, types)
        case c0.While(_, _, body):
            traverse_ast_types(body, types)
        case _:
            pass

def build_type_mapping(prog):
    map_types = {}
    args = prog.args or []
    if len(args) >= 1:
        map_types[args[0]] = c0.IntType()
    if len(args) >= 2:
        map_types[args[1]] = c0.ArrayType(c0.IntType())
    for s in prog.stmts:
        traverse_ast_types(s, map_types)
    return map_types



#ACTUAL WLP LOGIC

def check_in_bounds(arr, i):
    #checks 0 <= i && i < length(arr)
    return and_sym(leq(int_sym(0), i), c0.BinOp("<", i, c0.Length(arr)))

#remember the white boxes r requirements that need to be satisfied in every state
def check_pre_postcondition(precondition, post, white_boxes=None):
    
    if white_boxes is not None:
        return and_sym(precondition, post), white_boxes
    else:
        return and_sym(precondition, post), []

# wlp(alpha; beta)(Q) = wlp(alpha)(wlp(beta)(Q))
def wlp_sequence(commandList, Q, depth, env, context=None):
    result, all_vcs = Q, []
    for command in reversed(commandList):
        result, vcs = wlp(command, result, depth, env, context)
        all_vcs = vcs + all_vcs
    return result, all_vcs


# Compute wlp(command, Q) and accumulate VCs
def wlp(command, Q, depth=0, env=None, context=None):
    match command:
        case c0.Block(commandList):
            return wlp_sequence(commandList, Q, depth + 1, env, context)

        case c0.Assign(dest, c0.BinOp(op, a, b)) if op in ("/", "%"):
            safety = c0.BinOp("!=", b, int_sym(0))
            new_Q = c0_util.subst_exp(Q, dest, c0.BinOp(op, a, b))
            return and_sym(safety, new_Q), []

        case c0.Assign(dest, source):
            return c0_util.subst_exp(Q, dest, source), []

        case c0.Decl(type, name, init):
            if init is not None:
                return c0_util.subst_exp(Q, name, init), []
            if isinstance(type, c0.ArrayType):
                return c0_util.subst_exp(Q, name, c0.ArrMake(int_sym(0))), []
            return check_pre_postcondition(true_sym(), Q)

        case c0.AllocArray(dest, type, count):
            safety = leq(int_sym(0), count)
            new_Q = c0_util.subst_exp(Q, dest, c0.ArrMake(count))
            return and_sym(safety, new_Q), []

        case c0.ArrRead(dest, arr, i):
            safety = check_in_bounds(arr, i)
            new_Q = c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, i))
            return and_sym(safety, new_Q), []

        case c0.ArrWrite(arr, i, x):
            safety = check_in_bounds(arr, i)
            new_arr = c0.ArrSet(arr, i, x)
            new_Q = c0_util.subst_exp(Q, arr.name, new_arr)
            return and_sym(safety, new_Q), []

        case c0.If(cond, true_branch, false_branch):
            Q_true, vcs_t = wlp(true_branch, Q, depth + 1, env, context)
            if false_branch:
                Q_false, vcs_f = wlp(false_branch, Q, depth + 1, env, context)
            else:
                Q_false, vcs_f = Q, []
            branch = and_sym(implies_sym(cond, Q_true), implies_sym(not_sym(cond), Q_false))
            return branch, vcs_t + vcs_f

        case c0.While(cond, invariants, body):
            return wlp_while(cond, invariants, body, Q, depth, env, context)

        case c0.Assert(cond):
            return and_sym(cond, Q), []

        case c0.Error(msg):
            return true_sym(), []

        case c0.Return(val):
            if val is None:
                return Q, []
            return c0_util.subst_result(Q, val), []

        case _:
            return Q, []


def wlp_while(cond, invs, body, Q, depth, env=None, context=None):
    if not invs:
        inv = true_sym()
    else:
        inv = invs[0]
        for i in invs[1:]:
            inv = and_sym(inv, i)

    inv_and_cond = and_sym(inv, cond)
    if context is not None:
        loop_ctx = and_sym(context, inv_and_cond)
    else:
        loop_ctx = inv_and_cond

    body_wlp, nested_vcs = wlp(body, inv, depth + 1, env, context=loop_ctx)

    vcs = []
    vcs.append(implies_sym(loop_ctx, body_wlp))

    inv_and_not_cond = and_sym(inv, not_sym(cond))
    if context is not None:
        exit_ctx = and_sym(context, inv_and_not_cond)
    else:
        exit_ctx = inv_and_not_cond
    vcs.append(implies_sym(exit_ctx, Q))

    return inv, nested_vcs + vcs



def check_safety(
    prog: c0.Program,
) -> bool:

    c0_util.clear_subst_caches()
    prog = c0_util.rename_program(prog)

    env = build_type_mapping(prog)
    solver.set_var_types(env)

    pre = true_sym()
    for require in (prog.requires or []):
        pre = and_sym(pre, require)
    
    if prog.args and len(prog.args) == 2:
        argc_name, in_name = prog.args[0], prog.args[1]
        pre = and_sym(pre, leq(int_sym(0), c0.Var(argc_name)))
        pre = and_sym(pre, c0.BinOp("==", c0.Length(c0.Var(in_name)), c0.Var(argc_name)))

    post = true_sym()
    for ensure in (prog.ensures or []):
        post = and_sym(post, ensure)

    # need to split to run wlp on the body and substitute the 
    # return into postcondition
    commandList = prog.stmts
    if commandList:
        last_command = commandList[-1]
    else:
        last_command = None
    if isinstance(last_command, c0.Return):
        return_val = last_command.val
        body_commands = commandList[:-1]
    else:
        return_val = None
        body_commands = commandList

    if return_val is not None:
        post_subst = c0_util.subst_result(post, return_val)
    else:
        post_subst = post
    formula, vcs = wlp_sequence(body_commands, post_subst, 0, env, context=None)

    main_vc = implies_sym(pre, formula)
    all_vcs = [main_vc] + vcs
    for vc in all_vcs:
        if not solver.check_validity(c0_util.simplify(vc)):
            return False
    return True