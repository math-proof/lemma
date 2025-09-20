from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from Lemma import Set
    n = 5
    x = Symbol(etype=dtype.real, shape=(n,))
    i = Symbol(integer=True)

    Eq << apply(Cup[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.domain_defined)

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Set.Cup.eq.UnionCupS, cond={n})

    n -= 1
    Eq << Eq[-1].find(Cup).this.apply(Set.Cup.eq.UnionCupS, cond={n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cup).this.apply(Set.Cup.eq.UnionCupS, cond={n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cup).this.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-05
from . import setlimit
from . import outer
