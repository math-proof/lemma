from util import *


@apply
def apply(le_0, le_1):
    x, a = le_0.of(LessEqual)
    y, b = le_1.of(LessEqual)
    return LessEqual(Max(x, y), Max(a, b))


@prove
def prove(Eq):
    from Lemma import Algebra

    b, a, x, y = Symbol(real=True, given=True)
    Eq << apply(x <= a, y <= b)

    Eq << Algebra.GeMax.of.Ge.Ge.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2019-11-20
# updated on 2023-04-23
