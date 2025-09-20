from util import *


@apply
def apply(contains_p):
    arg_p, domain = contains_p.of(Element)
    p = arg_p.of(Arg)
    assert domain in Interval(-S.Pi, -S.Pi / 3, left_open=True)
    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    return Equal((p ** 3) ** (S.One / 3), p * w)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    p = Symbol(complex=True, given=True)
    Eq << apply(Element(Arg(p), Interval(-S.Pi, -S.Pi / 3, left_open=True)))

    Eq << Set.In.Mul.Icc.of.In.apply(Eq[0], 3)

    Eq << Set.InSub.of.In_Icc.apply(Eq[-1], S.Pi)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], S.Pi * 2)

    Eq << Set.EqCeil.of.In_Ioc.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[1].this.lhs.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.find(Arg).apply(Algebra.Arg.Pow.eq.Add)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.find(Exp[Add]).apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Expr.eq.AddRe_MulIIm)

    # Eq << Eq[-1] / Eq[1].rhs.args[1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.MulAbs_ExpMulIArg)


if __name__ == '__main__':
    run()
# created on 2021-03-08
