from util import *


@apply
def apply(given):
    dx, dy = given.of(Expr ** 2 < Expr ** 2)

    y2, x01_mean = dx.of(Expr - Expr)
    S[y2 * 2 / 3], y01_mean = dy.of(Expr - Expr)

    y01_mean *= 3
    y0, y1 = y01_mean.of(Add)

    x01_mean *= 2
    x0, x1 = x01_mean.of(Add)

    return Less(((x0 - x1) ** 2 + (x1 - y2) ** 2 + (y2 - x0) ** 2) / 3 + (y0 - y1) ** 2 / 2,
                (x0 - x1) ** 2 / 2 + ((y0 - y1) ** 2 + (y1 - y2) ** 2 + (y2 - y0) ** 2) / 3)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x0, x1, y0, y1, y2 = Symbol(real=True)
    Eq << apply((y2 - (x0 + x1) / 2) ** 2 < (y2 - (y0 + y1 + y2) / 3) ** 2)

    Eq << Eq[0] * 9

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Square)

    Eq.lt = Eq[-1].this.rhs.apply(Algebra.Mul.eq.Square)

    x1_ = Symbol('x1', y2 - x1)
    x0_ = Symbol('x0', y2 - x0)
    Eq.x0_defintion = x0_.this.definition + x0 - x0_

    Eq.x1_defintion = x1_.this.definition + x1 - x1_

    Eq << Eq.lt.lhs.this.subs(Eq.x0_defintion, Eq.x1_defintion)

    Eq << Eq[-1].this.rhs.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].subs(x0_.this.definition, x1_.this.definition)

    Eq.lt = Eq.lt.subs(Eq[-1])

    y1_ = Symbol('y1', y2 - y1)
    y0_ = Symbol('y0', y2 - y0)
    Eq << y0_.this.definition + y0 - y0_

    Eq << y1_.this.definition + y1 - y1_

    Eq << Eq.lt.rhs.this.subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].subs(y0_.this.definition, y1_.this.definition)

    Eq << Eq.lt.subs(Eq[-1])

    Eq << Algebra.Mul.eq.Add.Square.apply(Eq[-1].rhs.find(Mul) / 2)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1] + (y0 - y1) ** 2

    Eq.lt = Eq[-1] / 2

    Eq << Eq[1] * 3

    Eq << Eq[-1] - Eq[-1].rhs.args[-1] - (y0 - y1) ** 2

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Square.Neg)

    Eq.le = LessEqual(Eq[-1].lhs, Eq.lt.lhs, plausible=True)

    Eq << Eq.le.this.apply(Nat.LeAddS.Is.Le)

    Eq << Eq[-1].subs(Eq.x0_defintion, Eq.x1_defintion)

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Le.given.Ge_0.apply(Eq[-1])

    Eq << Eq[-1] / 5 * 8

    Eq << Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(x0_ + x1_)

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq.lt, Eq.le)





if __name__ == '__main__':
    run()

# created on 2020-01-02
# updated on 2023-05-20
