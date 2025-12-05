from util import *


@apply
def apply(all_lt, subset, A):
    ((d, j), (S[d], i)), (S[j], S[0], S[i]), (S[i], S[0], m) = all_lt.of(All[Indexed < Indexed])
    cup, (S[0], n) = subset.of(Subset[Expr, Range])
    (d, j), (S[j], S[0], S[m]) = cup.of(Cup[FiniteSet[Indexed]])
    return Equal(softmax(A + (Stack[j:m, i:n](Bool(i > d[j])) - 1) * oo), exp(A) * Stack[i:n](Stack[j:m](Bool(i > d[j])) / ReducedSum(exp(A[i, ReducedArgMax(d - n * Stack[j:m](Bool(d[j] >= i)) - i):]))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Bool, Vector

    n, m = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, m), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    s = d[:m].cup_finiteset(j)
    Eq << apply(
        All[j:i, i:m](d[j] < d[i]),
        Subset(s, Range(n)),
        A)

    z = Symbol(Eq[-1].lhs)
    Ξ = Eq[-1].find(Stack)
    i = Ξ.variables[-1]
    Ξ = Symbol(Ξ)
    Eq.ksi_def = Ξ.this.definition

    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(A) * Ξ).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Tensor.Softmax.eq.Div_SumExp)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i]

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Vector.Sum.eq.Sum_Get, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.absorb)

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.domain_defined, simplify=None)

    Eq << Algebra.Eq.Sum.ReducedArgMax.of.All_Lt.Subset_Cup.apply(Eq[0], Eq[1], lambda i, j: exp(A[i, j]))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-26
# updated on 2023-03-19

