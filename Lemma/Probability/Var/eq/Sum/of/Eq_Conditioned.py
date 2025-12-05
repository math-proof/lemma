from util import *


@apply
def apply(eq_conditioned, n=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    if n is None:
        n = k
    return Equal(Variance(ReducedSum(x[:n])), Sum[k:n](Variance(x[k])))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool, Finset, Finset, Finset, Vector

    x = Symbol(real=True, shape=(oo,), random=True)
    n = Symbol(integer=True)
    Eq << apply(Equal(x[n] | x[:n], x[n]))

    Eq << Eq[1].lhs.this.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.rhs.apply(Probability.Var.Sum.eq.Add.Sum)

    Eq.eq_var = Eq[-1].this.find(Sum[2]).apply(Finset.Sum_Add.eq.AddSumS)

    j, i = Eq.eq_var.find(Sum[2]).variables
    Eq << Probability.Imp.Eq_0.Cov.of.Eq_Conditioned.apply(Eq[0], j)

    Eq.infer = Eq[-1].subs(n, i)

    Eq << Eq.eq_var.this.find(Sum[2]).apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.infer, Eq[-1].find(Piecewise))

    Eq << Eq[-2].subs(Eq[-1])

    t = Symbol(integer=True)
    Eq.infer = Eq.infer.subs(i, t).subs(j, i).subs(t, j)

    Eq << Eq[-1].this.find(Sum[2]).apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.infer, Eq[-1].find(Piecewise))

    Eq << Eq[-2].subs(Eq[-1])


    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.infer, Eq[-1].find(Piecewise))
    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-19

# updated on 2023-05-02
