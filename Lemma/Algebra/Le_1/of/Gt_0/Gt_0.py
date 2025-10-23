from util import *


@apply
def apply(gt_zero_a, gt_zero_b):
    a = gt_zero_a.of(ReducedSum[Expr ** 2] > 0)
    b = gt_zero_b.of(ReducedSum[Expr ** 2] > 0)
    return abs(ReducedSum(a * b)) / (sqrt(ReducedSum(a ** 2)) * sqrt(ReducedSum(b ** 2))) <= 1


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat, Nat, Nat

    n = Symbol(domain=Range(2, oo))
    a, b = Symbol(shape=(n,), real=True, given=True)
    Eq << apply(ReducedSum(a ** 2) > 0, ReducedSum(b ** 2) > 0)

    Eq << Nat.Ne.of.Gt.apply(Eq[0])

    Eq << Nat.Ne.of.Gt.apply(Eq[1])

    Eq << ~Eq[2]

    Eq <<= Eq[-1] & Eq[-2] & Eq[-3]

    Eq << Bool.Cond.of.And.apply(Eq[-1], -1)

    Eq << Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[0] * Eq[1])

    Eq << Algebra.GtMul.of.Gt_0.Gt.apply(Eq[-1], Eq[-2])

    Eq << Algebra.GtSquare.of.Gt_0.Gt.apply(Eq[-2], Eq[-1])

    Eq << Algebra.SquareReducedSum.le.MulReducedSumS.Cauchy.apply(a, b)

    Eq << ~Eq[-1]





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2025-04-20
