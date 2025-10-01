from util import *


@apply
def apply(self):
    (sgm, sgm_t), n = self.of((Expr - Expr) / Expr)
    n += 1
    (xi, xj), (j, S[0], i), (S[i], S[0], S[n]) = sgm.of(Sum[(Expr - Expr) ** 2])
    (_xi, xt), (_i, S[0], S[n]) = sgm_t.of(Sum[(Expr - Expr) ** 2])
    x, t = xt.of(Indexed)

    assert _xi == x[_i]
    if xi._has(j):
        xi, xi = xj, xi

    assert xi == x[i]
    assert xj == x[j]

    assert 0 <= t < n

    return Equal(self, Sum[i:n]((x[i] - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2) - (xt - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x = Symbol(integer=True, shape=(oo,))
    t = Symbol(domain=Range(n))
    Eq << apply((Sum[j:i, i:n]((x[i] - x[j]) ** 2) - Sum[i:n]((x[i] - x[t]) ** 2)) / (n - 1))

    y = Symbol(Stack[i:n - 1](Piecewise((x[i], i < t),(x[i + 1], True))))
    Eq << y[i].this.definition

    Eq.y_sum = Algebra.EqSum.of.Eq_Ite.apply(Eq[1], Sum[i:n-1](y[i]))

    Eq << Algebra.Sum.Square.eq.Div.Sum.Square.apply(Sum[i:n-1]((y[i] - Sum[i:n - 1](y[i]) / (n - 1)) ** 2))

    Eq << Eq[-1].subs(Eq.y_sum).reversed

    Eq << Algebra.EqSum.of.Eq_Ite.apply(Eq[1], Eq[-1].rhs)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Sum_SquareSub.eq.Sub_SquareSum.apply(Eq[-1].lhs.args[1])

    Eq << Eq[-1].subs(Eq.y_sum)

    Eq << Algebra.EqSum.of.Eq_Ite.apply(Eq[1], Sum[i:n - 1](y[i] ** 2))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Add ** 2).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[0].lhs.find(Sum).this.apply(Algebra.Sum_SquareSub.eq.Sub_SquareSum)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[0].lhs.find(-~Sum).this.expr.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-3] + Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, lhs=slice(0, None, 2))

    Eq << Eq[0].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2019-11-27
# updated on 2023-05-20
