from util import *


@apply
def apply(*eqs, cond=None):
    matched = []
    unmatch = []

    for eq in eqs:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, And(*matched))


@prove
def prove(Eq):
    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply((a < b) | (c < d), (f(x) < g(y)) | (c < d), (x < y) | (c < d), cond=c < d)

    Eq <<= Eq[0] & Eq[1] & Eq[2]






if __name__ == '__main__':
    run()
# created on 2021-09-09
