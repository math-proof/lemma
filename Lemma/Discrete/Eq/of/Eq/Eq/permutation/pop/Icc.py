from util import *


@apply
def apply(cup_finiteset_equality, last_element_equality):
    from Lemma.Set.Eq.given.Eq.Cup.Finset import of_cup_finiteset
    if last_element_equality.lhs.is_Cup:
        last_element_equality, cup_finiteset_equality = cup_finiteset_equality, last_element_equality

    p, n = last_element_equality.lhs.of(Indexed)
    S[n] = last_element_equality.rhs

    cup_finiteset, S[Range(n + 1)] = cup_finiteset_equality.of(Equal)
    S[p[:n + 1]] = of_cup_finiteset(cup_finiteset)

    return Equal(p[:n].cup_finiteset(), Range(n))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    p = Symbol(shape=(oo,), integer=True, nonnegative=True, given=True)
    Eq << apply(Equal(p[:n + 1].cup_finiteset(), Range(n + 1)),
                Equal(p[n], n))

    Eq << Eq[0].this.lhs.apply(Set.Cup.eq.UnionCupS, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Set.EqSDiff.of.Eq.apply(Eq[-1], {n})

    Eq << Eq[2].subs(Eq[-1].reversed).reversed

    Eq.plausible = NotElement(n, Eq[-1].rhs, plausible=True)

    Eq << ~Eq.plausible

    Eq << Eq[-1].apply(Set.Any_In.of.In_Cup)

    i = Eq[-1].variable
    _i = i.copy(domain=Range(n))
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq[0].lhs.this.apply(Set.Cup.eq.UnionCupS, cond={_i, n})

    Eq << Eq[-1].this.rhs.args[0].apply(Set.Cup.eq.Union.doit.setlimit, evaluate=False)

    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq[-3].reversed, Eq[-1])

    Eq.paradox = Eq[-1].subs(Eq[1])

    Eq << Set.CardUnion.le.AddCardS.apply(*Eq.paradox.expr.rhs.args)

    Eq << Set.CardCup.le.Sum_Card.apply(*Eq.paradox.expr.rhs.args[1].args)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.LeAddS.Is.Le)

    Eq << Eq.paradox.this.expr.apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq[-1].reversed, Eq[-3])

    Eq << Set.EqSDiff.of.NotIn.apply(Eq.plausible)





if __name__ == '__main__':
    run()
# created on 2020-07-08
# updated on 2023-05-15
