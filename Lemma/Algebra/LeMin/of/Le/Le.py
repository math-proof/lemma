from util import *


@apply
def apply(le_a, le_b):
    x, a = le_a.of(LessEqual)
    y, b = le_b.of(LessEqual)
    return Min(x, y) <= Min(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(x <= a, y <= b)

    Eq << Algebra.GeMin.of.Ge.Ge.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-11-20
# updated on 2023-04-23
