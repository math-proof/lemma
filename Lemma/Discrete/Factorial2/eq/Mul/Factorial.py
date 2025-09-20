from util import *


@apply
def apply(self):
    n = self.of(Factorial2)
    assert n.is_even
    assert n >= 0
    n /= 2
    return Equal(self, Factorial(n) * 2 ** n)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Factorial2(n * 2))

    Eq << Eq[-1].this.lhs.apply(Discrete.Factorial2.eq.Prod)

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Mul.scale, S.Half)

    Eq << Eq[-1].this.rhs.apply(Discrete.Factorial.eq.Prod)

    i = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.limits.subst.Neg, i, n - i)
    # https://en.wikipedia.org/wiki/Double_factorial



if __name__ == '__main__':
    run()
# created on 2023-06-03
