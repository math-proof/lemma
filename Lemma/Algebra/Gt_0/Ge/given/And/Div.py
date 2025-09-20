from util import *


@apply
def apply(gt, ge):
    a, b = ge.of(GreaterEqual)
    x = gt.of(Expr > 0)
    return gt, GreaterEqual((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, GreaterEqual(x + y, z))

    Eq << Algebra.GeMul.of.Gt_0.Ge.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2023-10-03
