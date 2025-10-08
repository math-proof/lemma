from util import *


@apply
def apply(n):
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    return Equal(Card(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n)))), factorial(n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool

    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(n)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.arg.limits[0][1].simplify()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Discrete.Cup.eq.Condset.P2Q_union.apply(n)

    Q = Eq[-1].lhs.expr.base
    Eq << Eq[-1].apply(Set.EqCard.of.Eq)

    Eq << Discrete.Abs.Cup.eq.Sum.Abs.permutation.nonoverlapping.apply(n, Q=Q)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Discrete.Abs.Condset.inbetween.apply(n, Q=Q)

    P_quote = Eq[-1].rhs.arg
    Eq << Eq[-2].this.rhs.expr.subs(Eq[-1])

    Eq << Discrete.Abs.Condset.last.apply(n, P_quote=P_quote)

    Eq.P_definition = Eq[-1].lhs.arg.this.definition

    Eq.recursion = Eq[-2].subs(Eq[-1].reversed)

    Eq.Pn1_definition = Eq.recursion.lhs.arg.this.definition

    Eq << Eq[0].subs(Eq.P_definition.reversed)

    Eq << Eq.recursion.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Discrete.Mul.eq.Factorial)

    Eq << Eq.induct.subs(Eq.Pn1_definition.reversed)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-08-07
