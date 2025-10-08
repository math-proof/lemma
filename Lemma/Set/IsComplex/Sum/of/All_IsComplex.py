from util import *


@apply
def apply(all_is_complex):
    (expr, C), *limits = all_is_complex.of(All[Element])
    assert C in S.Complexes
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset

    return Element(Sum(expr, *limits), S.Complexes)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    x = Symbol(super_complex=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, given=False, nonnegative=True)
    Eq << apply(All[i:n](Element(x[i], S.Complexes)))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[2], cond=Element(x[n], S.Complexes))

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Eq[-1].this.rhs.apply(Set.IsComplex.Add.of.IsComplex.IsComplex)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.push)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=n, start=0)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-05-03
# updated on 2023-05-20
