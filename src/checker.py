#!/usr/bin/env python

import ast
import sys
import z3

from ast_to_z3_expr import ExpToZ3

str_to_z3_type = {
    'int': z3.Int,
    'bool': z3.Bool
}


def parse_cond(expr_str, vars):
    exp_ast = ast.parse(expr_str).body
    assert len(exp_ast) == 1, ("Wrong expr in cond!")
    exp_ast = exp_ast[0].value
    to_z3_visitor = ExpToZ3(vars)
    to_z3_visitor.visit(exp_ast)
    assert len(to_z3_visitor.res) == 1
    return to_z3_visitor.pop_result()


class CheckLambdaVisitor(ast.NodeVisitor):
    def visit_Call(self, e):
        if e.func.id != '_define':
            # skip
            return

        if len(e.args) != 4:
            raise Exception("Wrong number of args!")

        type_def, pre_cond, post_cond, func = e.args

        arg_names = list(map(lambda a: a.arg, func.args.args))

        func_args_types, func_ret_type = parse_type_def(type_def.s)

        assert len(func_args_types) == len(arg_names), (
            "Function annotation mismatch (at: %d)" % e.lineno)
        func_args = zip(arg_names, func_args_types)

        z3_vars = {}
        for var_name, var_type in func_args:
            z3_type = str_to_z3_type[var_type]
            z3_vars[var_name] = z3_type(var_name)

        z3_type = str_to_z3_type[func_ret_type]
        z3_vars['ret'] = z3_type('ret')

        pre_cond = parse_cond(pre_cond.s, z3_vars)
        post_cond = parse_cond(post_cond.s, z3_vars)

        v = ExpToZ3(z3_vars)
        v.visit(func.body)
        res = v.pop_result()

        solver = z3.Solver()
        solver.add(pre_cond)
        solver.add(res == z3_vars['ret'])
        solver.add(z3.Not(post_cond))
        check = solver.check()

        if check == z3.sat:
            print("NOT SAFE!")
            print(solver.model())
        else:
            print("SAFE.")


def parse_type_def(type_def):
    annots = map(str.strip, type_def.split('->'))
    *args, ret = (list(annots))
    return (args, ret)


def main():
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    st = ast.parse(s, fname)

    v = CheckLambdaVisitor()
    v.visit(st)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
