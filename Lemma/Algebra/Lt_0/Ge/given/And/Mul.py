from util import *


@apply
def apply(lt_zero, ge):
    a, b = ge.of(GreaterEqual)
    x = lt_zero.of(Expr < 0)
    return lt_zero, LessEqual((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x < 0, GreaterEqual(x + y, z))

    Eq << Algebra.GeDiv.of.Lt_0.Le.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2023-10-03
