from util import *


@apply
def apply(cup_finiteset_equality, last_element_equality):
    from Lemma.Set.Eq.given.Eq.Cup.Finset import of_cup_finiteset

    if last_element_equality.lhs.is_Cup:
        last_element_equality, cup_finiteset_equality = cup_finiteset_equality, last_element_equality
    p, n = last_element_equality.lhs.of(Indexed)
    a, S[n] = last_element_equality.rhs.of(Indexed)

    cup_finiteset_p, cup_finiteset_a = cup_finiteset_equality.of(Equal)
    S[p[:n + 1]] = of_cup_finiteset(cup_finiteset_p)
    S[a[:n + 1]] = of_cup_finiteset(cup_finiteset_a)

    return Equal(p[:n].cup_finiteset(), a[:n].cup_finiteset())


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    p, a = Symbol(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(Equal(p[:n + 1].cup_finiteset(), a[:n + 1].cup_finiteset()),
                Equal(p[n], a[n]))

    Eq << Eq[0].this.lhs.apply(Set.Cup.eq.UnionCupS, cond=slice(-1))

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.UnionCupS, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Set.EqSDiff.of.Eq.apply(Eq[-1], {a[n]})

    return
    Eq << Eq[2].subs(Eq[-1].reversed).reversed
    Eq.plausible = NotElement(n, Eq[-1].rhs, plausible=True)
    Eq << ~Eq.plausible
    Eq << Eq[-1].apply(Set.element.then.any_contains.split.cup)
    i = Eq[-1].variable
    _i = i.copy(domain=Range(n))
    Eq << Eq[-1].limits_subs(i, _i)
    Eq << Eq[0].lhs.this.split({_i, n})
    Eq.paradox = Eq[-1].subs(Eq[-2].reversed).subs(Eq[1])
    Eq << Set.then.le.Union.apply(*Eq.paradox.expr.rhs.args)
    Eq << Set.then.le.cup.apply(*Eq.paradox.expr.rhs.args[1].args)
    Eq << Eq[-2] + Eq[-1]
    Eq << Eq.paradox.apply(Algebra.eq.then.eq.abs)
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-3].subs(Eq[-1].reversed)
    Eq << Set.notcontains.then.Eq.Complement.apply(Eq.plausible)


if __name__ == '__main__':
    run()
# created on 2020-10-22
