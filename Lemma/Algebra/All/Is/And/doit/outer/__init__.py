from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit.outer import doit
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Set
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    Eq << apply(All[j:f(i), i:n](x[i, j] > 0))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Set.All.Is.AllInter.AllSDiff, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(Set.All.Is.AllInter.AllSDiff, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(Set.All.Is.AllInter.AllSDiff, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(Set.All.Is.AllInter.AllSDiff, cond={n})


if __name__ == '__main__':
    run()

# created on 2018-12-21

from . import setlimit
