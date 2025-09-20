from util import *


@apply
def apply(gt_zero, gt):
    a, b = gt.of(Greater)
    x = gt_zero.of(Expr > 0)
    return gt_zero, Greater((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, Greater(x + y, z))

    Eq << Algebra.GtDiv.of.Gt_0.Gt.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2023-10-03
