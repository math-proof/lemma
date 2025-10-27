from util import *


@apply
def apply(is_nonzero, q):
    p = is_nonzero.of(Unequal[0])

    delta = 4 * p ** 3 / 27 + q ** 2

    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    return Equal(Ceil(3 * Arg(U ** (S.One / 3) * V ** (S.One / 3)) / (S.Pi * 2) - S.One / 2), Piecewise((0, Equal(Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Set, Bool, Nat, Int

    p, q = Symbol(complex=True, given=True)
    Eq << apply(Unequal(p, 0), q)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = Symbol(sqrt(delta) - q)
    V = Symbol(-sqrt(delta) - q)
    Eq.U, Eq.V = U.this.definition, V.this.definition

    Eq << Eq.U * Eq.V

    Eq.UV = Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[1].subs(Eq.U.reversed, Eq.V.reversed)

    Eq << Eq[-1].this.find(Arg[~Mul[Pow]]).apply(Algebra.Mul.Root.eq.Mul.Ite.cubic_root)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.find(Arg[Piecewise]).apply(Algebra.Arg.Ite.eq.Ite)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.find(Ceil[Piecewise]).apply(Algebra.Ceil.Ite.eq.Ite)

    Eq.eq = Eq[-1].this.find(Ceil[~Mul]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Or(*Eq[-1].find(Or).args[:2]).this.apply(Nat.Mul.eq.Zero.of.OrEqS)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.rhs * (-Integer(27) / 4)

    Eq.suffice = Eq[-1].this.rhs.apply(Algebra.Eq_0.of.Pow.eq.Zero)

    Eq << Equal(U * V, 0).this.apply(Nat.OrEqS_0.of.Mul.eq.Zero)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.lhs * (-Integer(27) / 4)

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Zero.given.Eq_0)

    Eq <<= Eq.suffice & Eq[-1]

    Eq << Algebra.Cond.given.Cond.subst.Cond.apply(Eq.eq, old=Eq[-1].lhs, new=Eq[-1].rhs)

    Eq << Algebra.Cond.given.Cond.subst.Bool.apply(Eq[-1], cond=Eq[0], invert=True)

    Eq.p_cubic = Eq[-1].find(Pow[Mul]).this.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq.p_is_positive = Int.GtAbs_0.of.Ne_0.apply(Eq[0])

    Eq << Algebra.EqArg.of.Gt_0.apply(Eq.p_is_positive, Eq.p_cubic.find(Exp))

    Eq << Algebra.EqArg.of.Eq.apply(Eq.p_cubic)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.Arg.ExpI.eq.Mul.Arg)

    Eq << Eq[-1].this.find(Arg[Mul]).apply(Algebra.ArgMulPow.eq.SubMulArgMul)

    Eq << Eq[-6].subs(Eq[-1])

    Eq.eq_simplified = Eq[-1].this.find(Ceil[Add[~Mul[Add]]]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq.p_cubic * exp(S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << Algebra.EqArg.of.Gt_0.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << Algebra.EqArg.of.Eq.apply(Eq[-2])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq.p3_contains = Set.Arg.In.IocNegPiPi.apply(-p ** 3)

    Eq << Set.InAdd.of.In_Icc.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], 3, simplify=None)

    Eq << Set.Eq.Arg.ExpI.of.In.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(Algebra.ArgMulPow.eq.SubMulArgMul)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceil[Add[~Mul[Add]]]]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.eq_simplified = Eq[-1].this.find(Add[~Ceil]).apply(Algebra.CeilAddDiv_2.eq.AddCeilSub_Div12.of.IsOdd)

    Eq << Eq.p_cubic * exp(-S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << Algebra.EqArg.of.Gt_0.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << Algebra.EqArg.of.Eq.apply(Eq[-2])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Set.InSub.of.In_Icc.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], 3, simplify=None)

    Eq << Set.Eq.Arg.ExpI.of.In.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(Algebra.ArgMulPow.eq.SubMulArgMul)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceil[Add[~Mul[Add]]]]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Add[~Ceil]).apply(Algebra.CeilAddDiv_2.eq.AddCeilSub_Div12.of.IsOdd)





if __name__ == '__main__':
    run()
# created on 2018-11-08
# updated on 2022-01-23
