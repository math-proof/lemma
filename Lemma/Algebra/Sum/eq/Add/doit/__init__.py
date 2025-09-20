from util import *


def doit(Sum, self):
    xi, limit = self.of(Sum)
    try:
        i, a, b = limit
    except:
        i, = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    assert i.is_integer

    diff = b - a
    assert diff == int(diff)

    sgm = Sum.identity(xi)
    for t in range(diff):
        sgm = Sum.operator(sgm, xi._subs(i, a + t))

    return sgm


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo, k))
    i = Symbol(integer=True)

    n = 5
    Eq << apply(Sum[i:n](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})


if __name__ == '__main__':
    run()

# created on 2018-04-29
from . import setlimit
from . import outer
