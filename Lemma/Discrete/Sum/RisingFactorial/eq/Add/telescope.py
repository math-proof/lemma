from util import *


@apply
def apply(self):
    (k, i), (k, S[1], n) = self.of(Sum[1 / RisingFactorial])
    n -= 1
    i -= 1
    assert i > 0
    return Equal(self, (1 / Factorial(i) - 1 / RisingFactorial(n + 1, i)) / i)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:1:n + 1](1 / RisingFactorial(k, i + 1)))

    Eq << RisingFactorial(k, i).this.apply(Discrete.RisingFactorial.eq.Mul.shift)

    Eq << RisingFactorial(k + 1, i).this.apply(Discrete.RisingFactorial.eq.Mul.pop)

    Eq << (1 / RisingFactorial(k, i) - 1 / RisingFactorial(k + 1, i)).this.subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].subs(Eq[1].reversed)

    Eq << Eq[0].this.lhs.expr.base.apply(Discrete.RisingFactorial.eq.Mul.pop)

    Eq << Eq[-1] * i

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.telescope)





    # https://en.wikipedia.org/wiki/Telescoping_series




if __name__ == '__main__':
    run()
# created on 2023-08-17
# updated on 2023-08-20
