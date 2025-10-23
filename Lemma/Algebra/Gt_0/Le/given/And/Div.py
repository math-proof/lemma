from util import *


@apply
def apply(gt, le):
    a, b = le.of(LessEqual)
    x = gt.of(Expr > 0)
    return gt, LessEqual((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, LessEqual(x + y, z))

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2023-10-03
