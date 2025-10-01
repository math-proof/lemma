from util import *


@apply
def apply(self):
    d, S[d] = self.of(Ceil[Sign / Expr])
    assert d.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    d = Symbol(integer=True, zero=False, given=True)
    Eq << apply(Ceil(sign(d) / d))

    Eq << Set.Eq_Ceil.given.In.Icc.apply(Eq[0])

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[-1])

    Eq << Eq[-2].this.find(Sign).apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1].this.find(Sign).apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1] * abs(d)

    Eq << ~Eq[-1].reversed

    Eq << Algebra.Le_Sub_1.of.Lt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-29
