from util import *


@apply
def apply(self):
    (xij, mean), j_limit, i_limit = self.of(Sum[Pow[Expr - Expr, 2]])
    j, S[0], n = j_limit
    i, S[0], m = i_limit
    sgm = mean * (m * n)
    S[xij], S[j_limit], S[i_limit] = sgm.of(Sum)
    return Equal(self, n * Sum[i:m]((Sum[j:n](xij) / n - mean) ** 2) + Sum[j:n, i:m]((xij - Sum[j:n](xij) / n) ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset

    i, j = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo, oo))
    Eq << apply(Sum[j:n, i:m]((x[i, j] - Sum[j:n, i:m](x[i, j]) / (m * n)) ** 2))

    x_bar = Symbol(r"\overline{x}", Sum[j:n, i:m](x[i, j]) / (m * n))
    _x_bar = Symbol(r"\overline{x'}", Stack[i:m](Sum[j:n](x[i, j])) / n)
    Eq <<= x_bar.this.definition, _x_bar[i].this.definition

    Eq <<= Eq[-2] * (m * n), Eq[-1] * n, Algebra.EqSumS.of.Eq.apply(Eq[-1], (i, 0, m))

    Eq.eq_sum = Eq[-3].reversed

    Eq.eq_sum_j = Eq[-2].reversed

    Eq.eq_sum_quote = Eq[-1].subs(Eq.eq_sum)

    Eq << Eq[0].subs(Eq[1].reversed, Eq[2].reversed, simplify=None)

    Eq << Eq[-1].this.find(Mul[~Sum]).apply(Algebra.Sum.limits.domain_defined)

    Eq << Sum[j:n, i:m]((x[i, j] - x_bar) ** 2).this.expr.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq.St = Eq[-1].subs(Eq.eq_sum)

    Eq << Sum[i:m]((_x_bar[i] - x_bar) ** 2).this.expr.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].subs(Eq.eq_sum_quote)

    Eq << Eq[-1] * n

    Eq.SA = Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Sum[j:n, i:m]((x[i, j] - _x_bar[i]) ** 2).this.expr.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Sum[Mul]).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].subs(Eq.eq_sum_j)

    Eq << Eq[-1] + Eq.SA

    Eq << Eq.St.subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2020-03-27
# updated on 2023-06-24
