from util import *


@apply
def apply(eq, a):
    Ξ = eq.of(Equal[Identity + BlockMatrix[BlockMatrix[1][Zeros, Ones], BlockMatrix[1][Ones, Zeros]]])
    return Equal(exp(a + (Ξ - 1) * oo), Ξ * exp(a))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Nat

    n = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    a = Symbol(shape=(n, n), real=True)
    Ξ = Symbol(real=True, shape=(n, n))
    Eq << apply(Equal(Ξ, Identity(n) + BlockMatrix([[Zeros(h, h), Ones(h, n - h)],
                                                [Ones(n - h, h), Zeros(n - h, n - h)]])), a)

    i, j = Symbol(integer=True)
    Ξ_quote = Symbol("Ξ'", Stack[j:n, i:n](functions.Bool(Equal(i, j) | (i < h) & (j >= h) | (i >= h) & (j < h))))
    Eq << Ξ_quote[i, j].this.definition

    Eq.Ξ_quote_definition = Eq[-1].this.rhs.apply(Bool.Bool.eq.Ite)

    Eq << Eq[0][i, j]

    Eq << Eq[-1].this.rhs.apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.args[1].expr.apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.args[0]().expr.args[1]().expr.simplify()

    Eq.Ξ_definition = Eq[-1].this.rhs.args[1]().expr.simplify()

    Eq << Eq.Ξ_definition.this.rhs.args[-1].expr.apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite, index=0)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.rhs.args[1].cond.apply(Algebra.And.collect, cond=i < h)

    Eq << Eq[-1].this.rhs.args[1].cond.apply(Algebra.And.collect, cond=j < h)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.Is.Or.collect, cond=Equal(i, j))

    Eq << Eq[-1].this.find(And).apply(Bool.And_Or.Is.OrAndS)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.Ξ_quote_definition, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(a) * Ξ_quote).reversed

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[1].reversed)





if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-29
# updated on 2022-02-19
