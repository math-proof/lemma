from util import *


@apply
def apply(ge, lt):
    b, x = ge.of(GreaterEqual)
    a, _x = lt.of(Less)
    if x != _x:
        assert a == b
        a, b = x, _x
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    Eq << apply(x >= b, x < a)

    Eq << Eq[1].reversed

    Eq << Algebra.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-06-04
# updated on 2023-04-24

