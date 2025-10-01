from util import *


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return LessEqual(Ceil(x / d) * d, x + d - 1, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)

    Eq << apply(x, d)

    Eq << Algebra.Ceil.lt.Add_1.apply(x / d)

    Eq << Eq[-1] * d

    Eq << Eq[-1].this.rhs.expand()

    Eq << Algebra.Le_Sub_1.of.Lt.apply(Eq[-1])

if __name__ == '__main__':
    run()

# created on 2019-10-01
