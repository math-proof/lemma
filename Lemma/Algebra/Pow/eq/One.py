from util import *


@apply
def apply(self):
    p = self.of(Pow[-1, Expr])
    n = next(iter(p.free_symbols))
    p = p.as_poly(n)
    assert p.degree() == 2
    c = p.nth(0)
    assert p.nth(2) == 1
    b = p.nth(1)
    t = (b - 1) / 2
    assert c == t ** 2 + t
    assert t.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    n, a = Symbol(integer=True)
    Eq << apply((-1) ** (n ** 2 + n * (2 * a + 1) + a ** 2 + a))

    t = Symbol(2 * binomial(n + a + 1, 2))
    Eq << t.this.definition

    Eq << Algebra.EqPowS.of.Eq.apply(Eq[1], base=-1)

    Eq << Eq[1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[2].subs(Eq[-1])

    Eq << Eq[0].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2020-02-29
