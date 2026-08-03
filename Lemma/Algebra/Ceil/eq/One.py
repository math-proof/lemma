from util import *


@apply
def apply(self):
    d, S[d] = self.of(Ceil[Sign / Expr])
    assert d.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat, Complex, Complex, Complex, Complex

    d = Symbol(integer=True, zero=False, given=True)
    Eq << apply(Ceil(sign(d) / d))

    Eq << Set.Ceil.eq.Add_1.given.In_Ioc.apply(Eq[0])

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Eq[-2].this.find(Sign).apply(Complex.Sign.eq.Ite__Div_Abs)

    Eq << Eq[-1].this.find(Sign).apply(Complex.Sign.eq.Ite__Div_Abs)

    Eq << Eq[-1] * abs(d)

    Eq << ~Eq[-1].reversed

    Eq << Nat.Le_Sub_1.of.Lt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-29
