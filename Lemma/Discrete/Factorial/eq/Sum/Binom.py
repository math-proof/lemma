from util import *


@apply
def apply(self, k=None):
    n = self.of(factorial)
    if k is None:
        k = self.generate_var(integer=True)
    return Equal(self, Sum[k:n + 1]((-1) ** (n - k) * k ** n * binomial(n, k)))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(factorial(n))

    x = Symbol(real=True)
    Eq << Discrete.Diff.eq.Sum.Binom.apply(Difference(x ** n, (x, n)))

    Eq << Eq[-1].this.lhs.apply(Discrete.Diff.eq.Factorial)

    Eq << Eq[-1].subs(x, 0)





if __name__ == '__main__':
    run()
# created on 2020-10-13
# updated on 2023-06-17
