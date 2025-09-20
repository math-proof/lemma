from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceil((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_Ceil.of.Gt_Arg)
    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_Arg.of.Eq_Ceil)


if __name__ == '__main__':
    run()
# created on 2018-10-31
