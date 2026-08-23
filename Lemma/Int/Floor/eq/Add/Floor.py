from util import *


@apply
def apply(self):
    x = self.of(Floor)
    x = 2 * x + 1
    assert x.is_integer

    return Equal(self, x - x // 2 - 1)


@prove
def prove(Eq):
    from Lemma import Int
    x = Symbol(integer=True)
    Eq << apply((x - 1) // 2)

    Eq << Eq[-1].this.lhs.apply(Int.Floor.eq.CeilDivAdd_Sign)

    Eq << Eq[-1].this.lhs.apply(Int.Ceil.eq.Add.Frac)

    Eq << Eq[-1] - x / 2

    Eq << Eq[-1].this.rhs.apply(Int.SubCeil.eq.FracNeg)

    Eq << Eq[-1].this.lhs.apply(Int.Frac.half)


if __name__ == '__main__':
    run()

# created on 2019-05-11
