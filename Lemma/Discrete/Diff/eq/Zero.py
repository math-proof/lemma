from util import *


@apply
def apply(self):
    (fx, d), (x, n) = self.of(Difference[Pow])
    assert not (fx - x)._has(x)
    assert d < n
    return Equal(self, 0)


@prove
def prove(Eq):
    from Lemma import Discrete

    x, delta = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    d = Symbol(domain=Range(n))
    Eq << apply(Difference((x + delta) ** d, (x, n)))

    Eq << Eq[-1].this.lhs.apply(Discrete.Diff.split, d)

    Eq << Eq[-1].this.find(Difference[Pow]).apply(Discrete.Diff.eq.Factorial)





if __name__ == '__main__':
    run()
# created on 2021-12-01
