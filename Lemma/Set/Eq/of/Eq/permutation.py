from util import *


@apply
def apply(given, x):
    p_cup_finiteset, interval = given.of(Equal)
    (p, i), (S[i], S[0], n) = p_cup_finiteset.of(Cup[FiniteSet[Indexed]])

    assert p_cup_finiteset == p[:n].cup_finiteset()
    S[0], S[n] = interval.args
    assert interval.right_open
    return Equal(Cup[i:n](x[p[i]].set), x[:n].cup_finiteset())


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    p, x = Symbol(integer=True, shape=(n,))
    Eq << apply(Equal(p.cup_finiteset(), Range(n)), x)

    A = Symbol(Eq[1].lhs)
    B = Symbol(Eq[1].rhs)
    Eq.A_definition = A.this.definition

    i = Eq[1].lhs.variable
    _i = Symbol('i', domain=Range(n))
    Eq.A_definition = Eq.A_definition.this.rhs.limits_subs(i, _i)

    j = Eq[1].rhs.variable
    _j = Symbol('j', domain=Range(n))
    Eq.B_definition = B.this.definition

    Eq.B_definition = Eq.B_definition.this.rhs.limits_subs(Eq.B_definition.rhs.variable, _j)

    Eq.subset = Subset(Eq.A_definition.rhs, Eq.B_definition.rhs, plausible=True)

    Eq << Set.SubsetCup.given.All_Subset.apply(Eq.subset)

    Eq << Eq[-1].apply(Set.In_Cup.given.Any_In)

    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], Eq[-1].variable, p[_i])

    Eq.supset = Supset(Eq.subset.lhs, Eq.subset.rhs, plausible=True)

    Eq << Set.Supset_Cup.given.All_Supset.apply(Eq.supset)

    Eq.definition = Eq[-1].apply(Set.In_Cup.given.Any_In)

    Eq << Discrete.And.of.Eq.index.apply(Eq[0], _j)

    index_j = Eq[-1].lhs.indices[0]
    Eq << Eq.definition.subs(Eq[-1].reversed)

    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], Eq[-1].variable, index_j)
    Eq << Algebra.Any.given.Cond.apply(Eq[-1])

    Eq <<= Eq.subset & Eq.supset

    Eq << Eq[-1].this.lhs.limits_subs(_i, i)

    Eq << Eq[-1].this.rhs.limits_subs(_j, j)

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.domain_defined)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.limits.domain_defined)


if __name__ == '__main__':
    run()

# created on 2020-09-14
