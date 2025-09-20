from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    s = Arg(x) + Arg(y)
    return Equal(Arg(x * y), s - Ceil(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << Algebra.GtAbs_0.of.Ne_0.apply(Eq[0])

    Eq << Algebra.GtAbs_0.of.Ne_0.apply(Eq[1])

    Eq.abs_is_positive = Eq[-1] * Eq[-2]

    Eq <<= Algebra.Expr.eq.MulAbs_ExpMulIArg.apply(x), Algebra.Expr.eq.MulAbs_ExpMulIArg.apply(y)

    Eq << Eq[-1] * Eq[-2]

    Eq << Algebra.EqArg.of.Eq.apply(Eq[-1])

    Eq << Algebra.EqArg.of.Gt_0.apply(Eq.abs_is_positive, Mul(*Eq[-1].rhs.arg.args[2:]))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq << Eq[-1].this.rhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil)


if __name__ == '__main__':
    run()
# created on 2018-10-25
