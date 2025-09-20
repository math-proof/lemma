from util import *


@apply
def apply(ne_zero, eq):
    a, b = eq.of(Equal)
    x = ne_zero.of(Unequal[0])

    return ne_zero, Equal((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(Unequal(x, 0), Equal(1 / x + y, z))

    Eq << Algebra.EqDivS.of.Eq.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.ratsimp()





if __name__ == '__main__':
    run()

# created on 2019-05-02
# updated on 2023-06-22
