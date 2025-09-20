from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit import doit
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)

    n = 5
    Eq << apply(All[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.split, cond={n})


if __name__ == '__main__':
    run()
# created on 2018-04-24

from . import outer
