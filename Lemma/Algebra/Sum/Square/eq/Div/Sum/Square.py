from util import *


@apply
def apply(self):
    function, limit = self.of(Sum)
    x_sub_x_means = function.of(Expr ** 2)

    try:
        i, S[0], n = limit
    except:
        i, = limit
        domain = function.domain_defined(i)
        S[0], n = domain.of(Range)

    assert i.is_integer

    xi, x_means = x_sub_x_means.of(Expr - Expr)

    x, S[i] = xi.of(Indexed)

    x_sum = x_means * n

    xi, limit = x_sum.of(Sum)

    try:
        j, S[0], S[n] = limit
    except:
        j, = limit
        domain = xi.domain_defined(j)
        S[0], S[n] = domain.of(Range)

    S[x], S[j] = xi.of(Indexed)

    if j == i:
        j = self.generate_var(excludes={i}, integer=True, var='j')

    return Equal(self, Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True, shape=(oo,))
    Eq << apply(Sum[i:n]((x[i] - Sum[j:n](x[j]) / n) ** 2))

    Eq << Eq[-1].this.lhs.expr.expand()

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Pow, Sum).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.lhs.find(Mul).args[2].apply(Algebra.Square.Sum.eq.Add.Sum)

    Eq << Eq[-1].this.lhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Sum, Pow).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1] * n

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()



    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.args[1].doit()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(j, i)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.rhs.apply(Finset.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.rhs.expr.expand()

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)




if __name__ == '__main__':
    run()

# created on 2019-11-15
# updated on 2023-04-28
