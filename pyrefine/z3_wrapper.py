import z3


def proof(assumptions, to_prove):
    solver = z3.Solver()
    solver.add(*assumptions)
    solver.add(z3.Not(to_prove))
    check = solver.check()

    if check == z3.unsat:
        return None
    if check == z3.sat:
        model = solver.model()
        return model
    return True
