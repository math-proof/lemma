from util import *



@apply
def apply(self):
    args = self.of(Max)

    x = []
    for arg in args:
        if arg.is_Ceil:
            x.append(arg.arg)
        elif arg.is_integer:
            x.append(arg)
        else:
            return

    return Equal(self, Ceil(Max(*x)))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)
    Eq << apply(Max(ceil(x), ceil(y)))

    Eq << Eq[0].apply(Algebra.Eq_Ceil.given.And)

    Eq <<= Algebra.Gt_Sub_.Ceil.One.apply(x), Algebra.Gt_Sub_.Ceil.One.apply(y)

    Eq << Algebra.GtMax.of.Gt.Gt.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Add)

    Eq << Eq[-1] + 1

if __name__ == '__main__':
    run()
# created on 2020-01-24
