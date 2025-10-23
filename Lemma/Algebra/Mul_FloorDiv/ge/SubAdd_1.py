from util import *


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return GreaterEqual(Floor(x / d) * d, x - d + 1, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)

    Eq << apply(x, d)

    Eq << Algebra.Floor.gt.Sub_1.apply(x / d)

    Eq << Eq[-1] * d

    Eq << Eq[-1].this.rhs.expand()

    Eq << Nat.Ge_Add_1.of.Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-27
