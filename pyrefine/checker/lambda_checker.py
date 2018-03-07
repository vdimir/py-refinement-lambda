import z3

from ..ast_parser.lambda_parser import get_lambdas_model


def check_all_lambdas(program_ast):
    models = get_lambdas_model(program_ast)
    for m in models:
        solver = z3.Solver()
        solver.add(m.pre_cond)
        solver.add(m.variables.get_var(m.ret_var_name) == m.body)
        solver.add(z3.Not(m.post_cond))
        check = solver.check()
        #
        if check == z3.sat:
            print("Wrong function at line: {}\nCounterexample: {}."
        .format(m.src_data['lineno'], solver.model()))
        else:
            print("SAFE.")
