from util import *


@apply
def apply(self, i=None):
    n2, n = self.of(Binomial)
    S[n * 2] = n2
    assert n.is_integer
    assert n >= 0
    if i is None:
        i = self.generate_var(integer=True)
    return Equal(self, Factorial2(2 * n - 1) * 2 ** n / (factorial(n)))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Binomial(n * 2, n), i)

    Eq << Eq[0].this.lhs.apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1] * factorial(n)

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Mul.Factorial2)

    Eq << Eq[-1].this.find(Factorial2).apply(Discrete.Factorial2.eq.Mul.Factorial)

    # https://reference.wolfram.com/language/ref/Factorial2.html



if __name__ == '__main__':
    run()
# created on 2023-06-03
