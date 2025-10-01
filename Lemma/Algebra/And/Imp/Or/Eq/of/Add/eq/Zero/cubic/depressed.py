from util import *


@apply
def apply(is_zero, x=None):
    from Lemma.Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    S[1], S[0], p, q = cubic_coefficient(fx, x=x)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    arg_p = Ceil(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)

    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    d = arg_p - arg_AB
    return Imply(Equal(d, 0), Equal(x, A + B) | Equal(x, A * w + B * ~w) | Equal(x, A * ~w + B * w)), Imply(Equal(d % 3, 1), Equal(x, A * w + B) | Equal(x, A * ~w + B * ~w) | Equal(x, A + B * w)), Imply(Equal(d % 3, 2), Equal(x, A * ~w + B) | Equal(x, A + B * ~w) | Equal(x, A * w + B * w))



@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x)

    Eq << Set.Arg.In.IocNegPiPi.apply(-p)

    Eq << Set.In.Mul.Icc.of.In.apply(Eq[-1], 3, simplify=None)

    Eq << Set.InSub.of.In_Icc.apply(Eq[-1], S.Pi, simplify=None)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], S.Pi * 2, simplify=None)

    Eq << Set.In_Ico.Ceil.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Set.Ico.eq.Finset)

    Eq << Set.Ite.In.Finset.apply(Eq[1].find(Piecewise))

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[-1])

    Eq << Set.In.Add.Finset.of.In.In.apply(Eq[-1], Eq[-3])

    V = Eq[-1].find(Arg[Add]).arg
    U = Eq[-1].find(Arg[2]).arg
    Eq.eq_peicewise = Algebra.Ceil.Arg.eq.Ite.apply(Eq[-1].find(Ceil)._subs(-p, U ** (S.One / 3) * V ** (S.One / 3)))

    Eq << Eq[-1].subs(Eq.eq_peicewise.reversed)

    Eq.ou = Set.Or.Eq.of.In_Finset.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[0]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Equal[-2] & Equal[0]).apply(Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[-1] & Equal[0]).apply(Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[0] & Equal[0]).apply(Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[S(1)] & Equal[0]).apply(Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[S(2)] & Equal[0]).apply(Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic, x, ret=0)

    # find Equal[S(1)] & Equal[S(-2)]
    Eq << Eq[-1].this.args[:3:2].apply(Logic.And_Or.of.OrAndS)

    # find Equal[S(-1)] & Equal[S(2)]
    Eq << Eq[-1].this.args[:2].apply(Logic.And_Or.of.OrAndS)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(Algebra.EqMod.of.Or_Eq)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(Algebra.EqMod.of.Or_Eq)

    Eq << Eq[-1].this.find(Equal[Ceil, Ceil]).apply(Algebra.Eq_0.Mod.of.Eq, 3, swap=True)

    Eq << Eq[-1].subs(Eq.eq_peicewise)

    Eq << Logic.And.Imp.of.Or.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(Algebra.Eq_0.Mod.of.Eq, 3)


if __name__ == '__main__':
    run()
# created on 2018-11-24
# updated on 2023-05-15

