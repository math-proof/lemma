from util import *


@apply
def apply(self):
    from Lemma.Algebra.Add.eq.Sum.limits.push import absorb
    return Equal(self, absorb(Cap, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set
    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(n + 1))
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:i:n](f(k)), f(n), evaluate=False))

    Eq << Eq[-1].this.rhs.apply(Set.Cap.eq.InterCapS, {n})


if __name__ == '__main__':
    run()
# created on 2021-04-27
