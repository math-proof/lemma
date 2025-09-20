from util import *


@apply
def apply(self):
    x, (S[x], *ab) = self.of(Integral[Exp[- Expr ** 2 / 2]])
    if ab:
        S[-oo], S[oo] = ab
    return Equal(self, sqrt(2 * pi))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    x = Symbol(real=True)
    Eq << apply(Integral[x](exp(-x ** 2 / 2)))

    y = Symbol(real=True)
    Eq << Eq[-1].lhs.this.limits_subs(x, y)

    Eq << Eq[-1] * Eq[-1].lhs

    Eq << Eq[-1].this.rhs.apply(Calculus.Mul.eq.Integral.as_multiple_limits)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.as_polar_coordinate)

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].apply(Algebra.EqSqrt.of.Eq)

    # https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/




if __name__ == '__main__':
    run()
# created on 2020-06-10
# updated on 2023-04-30
