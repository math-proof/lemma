from util import *


@apply
def apply(is_nonnegative, gt):
    x = is_nonnegative.of(Expr >= 0)
    y, S[x] = gt.of(Greater)
    return Greater(sqrt(y), sqrt(x))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << Nat.Gt.of.Gt.Ge.apply(Eq[1], Eq[0])

    Eq << Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GeSqrt_0.of.Ge_0.apply(Eq[0])

    Eq.is_positive = Algebra.GtAdd.of.Gt.Ge.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[1])

    Eq << Algebra.GtDiv.of.Gt_0.Gt.apply(Eq.is_positive, Eq[-1])

    Eq << ((sqrt(x) + sqrt(y))(-sqrt(x) + sqrt(y))).this.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq.is_positive, Eq[-1], simplify=None)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Algebra.Gt.given.Gt_0.apply(Eq[2])




if __name__ == '__main__':
    run()
# created on 2019-06-13
# updated on 2023-05-02
