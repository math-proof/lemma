from util import *


@apply
def apply(n, P_quote=None):
    from Lemma.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)
    if P_quote is None:
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))

    return Equal(Q[n], P_quote)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Discrete, Logic

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << Set.All_CupFinset.eq.Ico.apply(Eq[-1].lhs)

    Eq << Logic.All.All.of.All_And.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(Discrete.Eq.of.Eq.Eq.permutation.pop.Icc)

    Eq.all_P_quote = Eq[-1] & Eq[-3]

    Eq << Set.All_CupFinset.eq.Ico.apply(Eq[1].lhs)

    Eq << Logic.All.All.of.All_And.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(Discrete.Eq.of.Eq.Eq.permutation.push)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Set.Eq.of.All.All.apply(Eq.all_P_quote, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-07-09
