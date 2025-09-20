from util import *


@apply
def apply(n, Q=None):
    if Q is None:
        from Lemma.Discrete.All_And.mapping.Qu2v import predefined_symbols
        Q, w, x = predefined_symbols(n)
    else:
        x = Q.definition.expr.variable
    P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))

    t = Q.definition.variable
    return Equal(Card(Q[t]), Card(P_quote))


@prove
def prove(Eq):
    from Lemma import Discrete, Set
    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << Discrete.Condset.PQ_Equality.apply(n)

    Eq << Eq[2].subs(Eq[-1].reversed)

    u = Eq[-1].lhs.arg.indices[0]
    Eq << Discrete.All_And.mapping.Qu2v.apply(n, n, u)

    Eq << Discrete.All_And.mapping.Qu2v.apply(n, u, n)

    Eq << Set.Eq.of.All_And.All_And.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-08-01
