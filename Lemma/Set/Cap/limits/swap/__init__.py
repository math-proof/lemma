from util import *


@apply
def apply(self, i=0, j=1):
    from Lemma.Algebra.Sum.limits.swap import rewrite
    return Equal(self, rewrite(Cap, self, i, j))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cap[i:m, j:n](f[i] | g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Set.Cap.eq.InterCapS, {n})

    Eq.induct_dissected = Eq[-1].this.find(Intersection[~Cap]).apply(Set.Cap.eq.Inter.doit.outer.setlimit)

    s = Symbol(Cap[j:n + 1](f[i] | g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(Set.EqCap.of.Eq, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cap.eq.InterCapS, {n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.Cap.eq.Inter)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << Set.EqInter.of.Eq.apply(Eq[0], Eq[-1].find(Cap))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

# created on 2021-01-31
# updated on 2023-07-02
from . import intlimit
from . import subst
