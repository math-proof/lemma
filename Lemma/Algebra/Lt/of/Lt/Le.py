from util import *


@apply
def apply(lt, le):
    a, x = lt.of(Less)
    _x, b = le.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b)

    Eq << ~Eq[2]

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[-1], Eq[1])

    Eq <<= Eq[0] & Eq[-1]

    


if __name__ == '__main__':
    run()
# created on 2018-10-17

# updated on 2025-04-10
