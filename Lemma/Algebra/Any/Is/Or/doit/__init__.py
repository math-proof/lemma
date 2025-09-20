from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit import doit
    return doit(Any, self)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = 5
    Eq << apply(Any[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Any.Is.Or.Any.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.Is.Or.Any.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.Is.Or.Any.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.Is.Or.Any.split, cond={n})




if __name__ == '__main__':
    run()

# created on 2019-02-11
# updated on 2023-10-22
from . import outer
from . import setlimit
