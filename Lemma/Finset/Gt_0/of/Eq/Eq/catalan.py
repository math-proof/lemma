from util import *


def is_catalan_series(*given):
    C0_definition, Cn1_definition = given
    C0, S[1] = C0_definition.of(Equal)

    Cn1, summation = Cn1_definition.of(Equal)
    fk, (k, S[0], n1) = summation.of(Sum)

    n = n1 - 1

    Cn = Cn1._subs(n, n - 1)
    assert Cn._subs(n, 0) == C0

    S[Cn._subs(n, n - k)] = fk.of(Expr * Cn._subs(n, k))
    return Cn, n


@apply
def apply(eq, eq1):
    Cn, n = is_catalan_series(eq, eq1)
    return Greater(Cn, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True)
    n = Symbol(integer=True, given=False)
    C = Symbol(shape=(oo,), integer=True)
    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    Eq.initial = Algebra.Gt.of.Eq.apply(Eq[0], 0)

    k = Symbol(domain=Range(n + 1))
    Eq.induct = Eq[2].subs(n, n + 1)

    Eq.hypothsis_k = Eq[2].subs(n, k)

    Eq.hypothsis_nk = Algebra.Cond.of.Cond.subst.apply(Eq.hypothsis_k, k, n - k)

    Eq << Eq.hypothsis_nk * Eq.hypothsis_k

    Eq << Algebra.GtSum.of.Gt.apply(Eq[-1], (k,))

    Eq << Eq[-1].this.lhs.limits_subs(k, k.copy(domain=None))

    Eq << Eq[-1] + Eq[1]
    Eq << Eq[-1].this.apply(Algebra.Gt.transport)

    Eq << Imply(Eq.hypothsis_k, Eq.induct, plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.given.All, k)

    Eq << Bool.Cond.of.Cond.Imp.induct.second.split.All.apply(Eq.initial, Eq[-1], n=n)

    Eq << Eq[2].subs(n, k)


if __name__ == '__main__':
    run()

# created on 2020-10-18
