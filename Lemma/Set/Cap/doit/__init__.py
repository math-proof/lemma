from util import *


@apply
def apply(self):
    xi, limit = self.of(Sum)
    try:
        i, a, b = limit
    except:
        i, = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    diff = b - a
    assert diff == int(diff)

    sgm = Zeros(*xi.shape)
    for t in range(diff):
        sgm += xi._subs(i, a + t)

    return Equal(self, sgm)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = 5
    Eq << apply(Sum[i:n](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.AddSumS, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.AddSumS, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.AddSumS, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.AddSumS, cond={n})


if __name__ == '__main__':
    run()

# created on 2021-01-21
from . import inner
from . import outer
