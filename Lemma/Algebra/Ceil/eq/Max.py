from util import *


@apply
def apply(self):
    m = self.of(Ceil)
    args = m.of(Max)
    args = [ceil(arg) for arg in args]

    return Equal(self, Max(*args))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)
    Eq << apply(ceil(Max(x, y)))

    Eq << Eq[0].apply(Algebra.Eq_Ceil.given.And)

    Eq <<= Algebra.Gt_Sub_.Ceil.One.apply(x), Algebra.Gt_Sub_.Ceil.One.apply(y)

    Eq << Algebra.GtMax.of.Gt.Gt.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Add)

    Eq << Eq[-1] + 1


if __name__ == '__main__':
    run()
# created on 2019-03-10
