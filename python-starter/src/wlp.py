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
    # main(int argc, int[] in) → first arg int, second int[]
    arg_types = (c0.IntType(), c0.ArrayType(c0.IntType()))
    map_types = dict(zip(prog.args or [], arg_types))
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

#wlp(alpha; beta)(Q) = wlp(alpha)(wlp(beta)(Q))
#need to eval right to left
def wlp_sequence(commandList, Q, depth, env):
    result, all_whiteboxes = Q, []
    for command in reversed(commandList):
        result, wb = wlp(command, result, depth, env)
        all_whiteboxes = wb + all_whiteboxes
    return result, all_whiteboxes


#prove P -> [alpha]Q for all commands in c0
def wlp(command, Q, depth=0, env=None):
    match command:
        case c0.Block(commandList):
            return wlp_sequence(commandList, Q, depth + 1, env)

        case c0.Assign(dest, src):
            return check_pre_postcondition(denominator_zero_check(src), c0_util.subst_exp(Q, dest, src))
        
        case c0.Decl(type, name, init):
            if init is not None:
                precondition = denominator_zero_check(init)
                x = init
            else:
                precondition = true_sym()
                if isinstance(type, c0.ArrayType):
                    x = c0.ArrMake(int_sym(0))
                else:
                    x = int_sym(0)
            return check_pre_postcondition(precondition, c0_util.subst_exp(Q, name, x))
        
        case c0.AllocArray(dest, type, count):
            precondition = and_sym(denominator_zero_check(count), leq(int_sym(0), count))
            return check_pre_postcondition(precondition, c0_util.subst_exp(Q, dest, c0.ArrMake(count)))

        case c0.ArrRead(dest, arr, i):
            precondition = and_sym(denominator_zero_check(i), check_in_bounds(arr, i))
            post = c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, i))
            return check_pre_postcondition(precondition, post)

        case c0.ArrWrite(arr, i, x):
            precondition = and_sym(denominator_zero_check(i), and_sym(denominator_zero_check(x), check_in_bounds(arr, i)))
            if isinstance(arr, c0.Var):
                post = c0_util.subst_exp(Q, arr.name, c0.ArrSet(arr, i, x))
            else:
                post = Q
            return check_pre_postcondition(precondition, post)

        case c0.If(cond, true_branch, false_branch):
            Q_true, whitebox_true = wlp(true_branch, Q, depth + 1, env)
            if false_branch:
                Q_false, whitebox_f = wlp(false_branch, Q, depth + 1, env)
            else:
                Q_false, whitebox_f = Q, []
            precondition = denominator_zero_check(cond)
            branch = and_sym(implies_sym(cond, Q_true), implies_sym(not_sym(cond), Q_false))
            return and_sym(precondition, branch), whitebox_true + whitebox_f

        case c0.While(cond, invariants, body):
            return wlp_while(cond, invariants, body, Q, depth, env)

        case c0.Assert(cond):
            return check_pre_postcondition(and_sym(denominator_zero_check(cond), cond), Q)

        case c0.Error(msg):
            return true_sym(), []

        case c0.Return(val):
            return Q, []

        case _:
            return Q, []

def update_old_var(e, orig_to_new):
    #replace every variable in orig_to_new w/ new name in e
    out = e
    for orig, new in orig_to_new.items():
        out = c0_util.subst_exp(out, orig, c0.Var(new))
    return out

#wlp(while^J P alpha) Q = J AND whitebox(J and P -> wlp alpha J) 
#                           AND whitebox(J and (not)P -> Q)
def wlp_while(cond, invs, body, Q, depth, env=None):
    if not invs:
        return c0.BoolConst(False), []

    #join invariants -> formula first
    inv = invs[0]
    for i in invs[1:]:
        inv = and_sym(inv, i)

    #compute wlp(body, inv) to get the body's weakest precondition
    body_wlp, nested_whitebx = wlp(body, inv, depth + 1, env)

    modified_variables = set()
    variables = c0_util.get_defs(body)
    for v in variables:
        if env is None:
            continue
        if v not in env:
            continue
        if isinstance(env[v], c0.ArrayType):
            continue
        modified_variables.add(v)

    #set of variable names already used, so avoid 
    used_name = set()
    used_name.update(c0_util.vars_exp(inv))
    used_name.update(c0_util.vars_exp(cond))
    used_name.update(c0_util.vars_exp(body_wlp))
    used_name.update(c0_util.vars_exp(Q))
    used_name.update(c0_util.vars_stmt(body))

    #assign a new name to each modified vairables
    og_to_new = {}
    for var in sorted(modified_variables):
        fresh = c0_util.get_fresh_name(var + "_s", used_name)
        used_name.add(fresh)
        og_to_new[var] = fresh

    # give new names correct c0 types
    if env is not None:
        extra_types = {}
        for orig, fresh in og_to_new.items():
            if orig in env:
                extra_types[fresh] = env[orig]
        env.update(extra_types)
        solver.set_var_types(env)

    inv_sym = update_old_var(inv, og_to_new)
    cond_sym = update_old_var(cond, og_to_new)
    body_wlp_sym = update_old_var(body_wlp, og_to_new)
    Q_sym = update_old_var(Q, og_to_new)

    # loop preservation check
    cond_precondition = denominator_zero_check(cond_sym)
    preservation_antecedent = and_sym(inv_sym, and_sym(cond_sym, cond_precondition))
    preservation = implies_sym(preservation_antecedent, body_wlp_sym)

    # exit loop check
    exit_antecedent = and_sym(inv_sym, and_sym(not_sym(cond_sym), cond_precondition))
    exit_cond = implies_sym(exit_antecedent, Q_sym)

    new_variables = list(og_to_new.values())
    if new_variables:
        preservation = c0.ForAll(new_variables, preservation)
        exit_cond = c0.ForAll(new_variables, exit_cond)

    # checks from nested loops
    nested_loop_checks = []
    for whitebox in nested_whitebx:
        new_whitebox = update_old_var(whitebox, og_to_new)
        if new_variables:
            nested_loop_checks.append(c0.ForAll(new_variables, implies_sym(inv_sym, new_whitebox)))
        else:
            nested_loop_checks.append(new_whitebox)

    init_check = and_sym(denominator_zero_check(cond), inv)
    verify_all = nested_loop_checks + [preservation, exit_cond]
    return init_check, verify_all



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
    formula, white_boxes = wlp_sequence(body_commands, post_subst, 0, env)

    for wb in white_boxes:
        if not solver.check_validity(wb):
            return False

    vc = implies_sym(pre, formula)
    return solver.check_validity(vc)