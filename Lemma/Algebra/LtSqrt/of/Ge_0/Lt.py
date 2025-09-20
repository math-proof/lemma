from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x < M)

    Eq << Algebra.Gt.of.Ge.Lt.apply(Eq[0], Eq[1])

    Eq << Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GeSqrt_0.of.Ge_0.apply(Eq[0])

    Eq << Algebra.GtAdd.of.Gt.Ge.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt_0.of.Lt.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Algebra.LtDiv.of.Gt_0.Lt.apply(Eq[-3], Eq[-1])

    Eq << Algebra.Lt.of.Lt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-28
