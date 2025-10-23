from util import *


@apply
def apply(le, lt, evaluate=True):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, S[x], b = _x, b, a, x
    return Less(a, b, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True, given=True)
    Eq << apply(x <= a, b < x)

    Eq << ~Eq[-1]

    Eq << Algebra.Ge.of.Le.Ge.apply(Eq[0], Eq[-1])

    Eq <<= Eq[1] & Eq[-1]




if __name__ == '__main__':
    run()
# created on 2018-02-27
# updated on 2023-04-09

