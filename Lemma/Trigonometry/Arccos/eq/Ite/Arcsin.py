from util import *


@apply
def apply(self):
    x = self.of(acos)
    # assert x in Interval(-1, 1)
    return Equal(self, Piecewise((ArcSin(sqrt(1 - x ** 2)), x >= 0), (S.Pi - ArcSin(sqrt(1 - x ** 2)), True)))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Bool, Int

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(acos(x))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Arccos.eq.Add.Arcsin)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=x >= 0)

    Eq <<= Bool.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Bool.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.rhs.apply(Int.EqAdd.Is.Eq_Sub), Eq[-1].this.rhs.apply(Int.EqAdd.Is.Eq_Sub)

    Eq.is_nonnegative, Eq.is_negative = Eq[-2].this.rhs.reversed, Eq[-1].this.rhs.apply(Int.EqAdd.Is.Eq_Sub, rhs=0)

    Eq << Eq.is_negative.this.rhs.reversed

    Eq << -Eq[-1].this.rhs

    Eq << Eq.is_nonnegative.this.lhs.apply(Trigonometry.Eq.Add.Arcsin.of.Ge_0)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Eq.Add.Arcsin.of.Lt_0)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-14
