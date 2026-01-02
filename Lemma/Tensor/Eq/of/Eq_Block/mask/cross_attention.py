from util import *


@apply
def apply(eq, a):
    Ξ = eq.of(Equal[BlockMatrix[BlockMatrix[1][Zeros, Ones], BlockMatrix[1][Ones, Zeros]]])
    return Equal(exp(a + (Ξ - 1) * oo), Ξ * exp(a))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool

    n = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    a = Symbol(shape=(n, n), real=True)
    Ξ = Symbol(real=True, shape=(n, n))
    Eq << apply(Equal(Ξ, BlockMatrix([[Zeros(h, h), Ones(h, n - h)],
                                                [Ones(n - h, h), Zeros(n - h, n - h)]])), a)

    i, j = Symbol(integer=True)
    Ξ_quote = Symbol("Ξ'", Stack[j:n, i:n](functions.Bool((i < h) & (j >= h) | (i >= h) & (j < h))))
    Eq << Ξ_quote[i, j].this.definition

    Eq.Ξ_quote_definition = Eq[-1].this.rhs.apply(Bool.Bool.eq.Ite)

    Eq << Eq[0][i, j]

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Eq[-1].this.find(And).apply(Bool.And_Or.Is.OrAndS)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.Ξ_quote_definition, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.apply(exp(a) * Ξ_quote).reversed

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[1].reversed)




if __name__ == '__main__':
    run()
# created on 2022-02-20
