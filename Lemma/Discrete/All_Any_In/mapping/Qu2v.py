from util import *


@apply
def apply(n, u, v):
    from Lemma.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)
    j = w.definition.variables[0]
    x_quote = Symbol(w[n, j] @ x[:n + 1])
    return All[x[:n + 1]:Q[u]](Any[j:n + 1](Element(x_quote, Q[v])))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Discrete, Logic, Tensor

    n = Symbol(integer=True, positive=True)
    u, v = Symbol(domain=Range(n + 1))
    Eq << apply(n, u, v)

    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    Eq << Set.All_CupFinset.eq.Ico.apply(Q[u])

    Eq << Logic.All.of.All_And.apply(Eq[-1], 1)

    Eq.x_j_equality = Eq[-1].this.expr.apply(Discrete.Any.Eq.of.Eq.index, v)

    Eq << Eq.x_j_equality.this.expr.limits_subs(Eq.x_j_equality.expr.variable, j)

    Eq << Tensor.All_InDot.permutation.apply(n + 1, w=w)

    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)

    Eq << Set.All.of.Subset.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].subs(i, n)

    k = Eq[-1].expr.lhs.expr.arg.args[0].indices[-1]
    Eq << Eq[1][k].apply(Set.Eq.Cup.Finset.of.Eq, (k, 0, n + 1), simplify=False)

    Eq.x_n1_cup_finiteset = Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[1][n]

    Eq << Eq[0].subs(i, n)[n]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Algebra.All.Any.of.All_Any_Eq.Cond.subst.apply(Eq.x_j_equality, Eq[-1])

    Eq << Eq[-1].this.expr().expr.rhs.args[0].simplify()

    Eq <<= Eq.x_n1_cup_finiteset & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Logic.Any_And.of.Any.All)

    Eq << Eq[3].this.expr.expr.rhs.definition

    i = Eq[-1].find(Cup).variable
    k = Eq[-2].find(Cup).variable
    Eq << Eq[-1].this.find(Cup).limits_subs(i, k, simplify=False)


if __name__ == '__main__':
    run()
# created on 2020-11-01
