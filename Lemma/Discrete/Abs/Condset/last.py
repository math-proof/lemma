from util import *


@apply
def apply(n, P_quote=None):
    if P_quote is None:
        x = Symbol(shape=(oo,), integer=True, nonnegative=True)
        P_quote = Symbol(conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))
    else:
        x = P_quote.definition.variable.base

    P = Symbol(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n))))
    return Equal(Card(P), Card(P_quote))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic, Tensor

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    P_quote = Eq[1].lhs
    i = Symbol(integer=True)
    x_quote = Symbol("x'", Stack[i:n + 1](Piecewise((n, Equal(i, n)), (x[i], True))))
    Eq.x_quote_definition = x_quote.this.definition

    Eq << Eq.x_quote_definition[:n]

    Eq.mapping = Eq[-1].this.rhs().expr.simplify()

    Eq << Eq.x_quote_definition[i]

    Eq << Set.Eq.Cup.Finset.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq.x_quote_n_definition = Eq[-2].subs(i, n)

    Eq << Set.All_CupFinset.eq.Ico.apply(P)

    Eq << Algebra.All.of.All_Eq.Cond.subst.apply(Eq[-1], Eq[-2])

    Eq.P2P_quote = All[x[:n]:P](Element(x_quote, P_quote), plausible=True)

    Eq << Eq.P2P_quote.this.expr.rhs.definition

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Set.All_CupFinset.eq.Ico.apply(P_quote)

    Eq << Logic.All.All.of.All_And.apply(Eq[-1])

    Eq << Algebra.All.And.of.Cond.All.apply(Eq.x_quote_n_definition, Eq[-2], simplify=False)

    Eq << Eq[-1].this.expr.apply(Logic.Eq.of.Eq.Eq, reverse=True)

    Eq.mapping_quote = All[x[:n + 1]:P_quote](Equal(x_quote, x[:n + 1]), plausible=True)

    Eq << Eq.mapping_quote.this.expr.apply(Tensor.EqSliceS.given.EqSliceS.Eq.Lt)

    Eq << Logic.All_And.given.All.All.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.mapping)

    Eq << All[x[:n + 1]:P_quote](Element(x[:n], P), plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Set.Eq.of.All_In.All_In.All_Eq.All_Eq.apply(Eq[-1], Eq.P2P_quote, Eq.mapping_quote, Eq.mapping)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-08-01
