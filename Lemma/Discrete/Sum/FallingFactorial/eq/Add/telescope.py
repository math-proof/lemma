from util import *


@apply
def apply(self):
    (k, i), (k, S[0], n) = self.of(Sum[FallingFactorial])
    i = -i - 1
    assert i > 0
    assert n >= 0
    return Equal(self, (1 / Factorial(i) - FallingFactorial(n, -i)) / i)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Finset

    k = Symbol(integer=True)
    i, n = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:n](FallingFactorial(k, -i - 1)))

    Eq << Eq[0].this.find(FallingFactorial).apply(Discrete.FallingFactorial.eq.Inv.FallingFactorial)

    Eq << Eq[-1].this.lhs.expr.base.apply(Discrete.FallingFactorial.eq.Mul.shift)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, -i - 1)

    Eq << Eq[-1] * i

    Eq.final = Eq[-1].this.lhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << FallingFactorial(k - 1, i).this.apply(Discrete.FallingFactorial.eq.Mul.pop)

    Eq << FallingFactorial(k, i).this.apply(Discrete.FallingFactorial.eq.Mul.shift)

    Eq << (1 / FallingFactorial(k - 1, i) - 1 / FallingFactorial(k, i)).this.subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << Eq.final.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.telescope)

    Eq << Eq[-1].this.rhs.apply(Discrete.FallingFactorial.eq.Inv.FallingFactorial)

    # https://en.wikipedia.org/wiki/Telescoping_series




if __name__ == '__main__':
    run()
# created on 2023-08-17
# updated on 2023-08-20
