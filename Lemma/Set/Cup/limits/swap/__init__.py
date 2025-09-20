from util import *


@apply
def apply(self, i=0, j=1):
    from Lemma.Algebra.Sum.limits.swap import rewrite
    return Equal(self, rewrite(Cup, self, i, j))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cup[i:m, j:n](f[i] & g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq.induct_dissected = Eq[-1].this.find(Union[~Cup]).apply(Set.Cup.eq.Union.doit.outer.setlimit)

    s = Symbol(Cup[j:n + 1](f[i] & g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(Set.EqCupS.of.All_Eq.fin, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(Set.Inter.eq.Cup)

    Eq << Eq[-1].this.find(Intersection[~Cup]).apply(Set.Cup.eq.Union.doit.setlimit, simplify=None, evaluate=False)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.Cup.eq.Union)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << Set.EqUnionS.of.Eq.apply(Eq[0], Eq[-1].find(Cup))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

# created on 2021-02-11
# updated on 2023-07-02
from . import intlimit
from . import subst
