from util import *


@apply
def apply(self):
    from Lemma.Int.Abs.Neg import rewrite
    return Equal(self, rewrite(cos, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(complex=True)
    Eq << apply(cos(x - y))

    Eq << Eq[0].this.lhs.apply(Real.CosAdd.eq.SubCosCos_SinSin)

    Eq << Eq[-1].this.rhs.apply(Real.CosAdd.eq.SubCosCos_SinSin)





if __name__ == '__main__':
    run()
# created on 2023-05-20
# updated on 2023-11-26

from . import eq
