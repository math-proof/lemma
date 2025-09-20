from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    y, b = lt_b.of(Less)
    return Min(x, y) < Min(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(x < a, y < b)

    Eq << Algebra.GtMin.of.Gt.Gt.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()

# created on 2019-05-12
# updated on 2023-04-23
from . import both
