from util import *


@apply
def apply(contains_p):
    arg_p, domain = contains_p.of(Element)
    p = arg_p.of(Arg)
    assert domain in Interval(-S.Pi / 3, S.Pi / 3, left_open=True)
    return Equal((p ** 3) ** (S.One / 3), p)


@prove
def prove(Eq):
    from Lemma import Set, Nat, Int, Complex

    p = Symbol(complex=True, given=True)
    Eq << apply(Element(Arg(p), Interval(-S.Pi / 3, S.Pi / 3, left_open=True)))

    Eq << Nat.InMul.of.In_Ico.Gt_0.apply(Eq[0], 3)

    Eq << Int.InSub.of.In_Icc.apply(Eq[-1], S.Pi)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], S.Pi * 2)

    Eq << Set.EqCeil_0.of.In_Ioc.apply(Eq[-1])
    Eq << Eq[-1].this.find(Mul).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[1].this.lhs.apply(Complex.Pow_Inv.eq.Mul_ExpMulIDivArg)

    Eq << Eq[-1].this.find(Arg).apply(Complex.ArgPow.eq.SubMul_Arg)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.rhs.apply(Complex.Eq_MulNorm_ExpMulIArg)


if __name__ == '__main__':
    run()
# created on 2021-03-08
from . import third
from . import second
