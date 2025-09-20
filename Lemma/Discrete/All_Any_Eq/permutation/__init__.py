from util import *


@apply
def apply(a):
    n = a.shape[0]

    i = Symbol(integer=True)

    p = Symbol(shape=(oo,), etype=dtype.integer)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), a.cup_finiteset())))

    return All[p[:n]:P](Exists[i:n](Equal(p[i], a[n - 1])))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    n = Symbol(integer=True, positive=True)
    a = Symbol(etype=dtype.integer, shape=(n,))
    Eq << apply(a)

    Eq << Eq[1].subs(Eq[0])

    Eq << Algebra.All.limits_assert.apply(Eq[-1].limits)

    Eq << Element(a[n - 1], Eq[-1].rhs, plausible=True)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.UnionCupS, cond=slice(-1))

    Eq << Algebra.All.of.All_Eq.Cond.subst.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.Any_In.of.In_Cup)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()


# created on 2020-11-01

from . import basic
