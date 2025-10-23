from util import *


@apply
def apply(pow):
    z, n = pow.of(Arg[Pow])
    assert n.is_integer and n > 0
    return Equal(pow, Arg(z) * n - Ceil(Arg(z) * n / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    z = Symbol(complex=True, given=True)
    n = Symbol(integer=True, given=True, positive=True)
    Eq << apply(Arg(z ** n))

    Eq << Eq[-1].this.lhs.arg.base.apply(Algebra.Expr.eq.MulAbs_ExpMulIArg)

    Eq << Eq[-1].this.lhs.arg.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Unequal(z, 0))

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Int.GtAbs_0.of.Ne_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Pow.of.Gt_0, n)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqArg.of.Gt_0, Eq[-1].find(Exp))

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil)


if __name__ == '__main__':
    run()
# created on 2018-08-26
