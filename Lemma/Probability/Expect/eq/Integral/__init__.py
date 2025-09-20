from util import *


@apply
def apply(self):
    from Lemma.Probability.Expect.eq.Sum import extract
    assert not self.limits[-1][0].is_integer
    return Equal(self, extract(self))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    a, s = Symbol(real=True, random=True)
    Eq << apply(Expectation[a:θ](f(a), given=s))




if __name__ == '__main__':
    run()
# created on 2023-03-24
# updated on 2023-03-27

from . import reward
