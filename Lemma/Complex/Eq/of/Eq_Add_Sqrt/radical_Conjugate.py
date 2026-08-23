from util import *


@apply
def apply(eq):
    ((x, d), S[x]), a = eq.of(Equal[(Expr ** 2 + Expr) ** (S.One / 2) - Expr])
    return Equal(x, (d / a - a) / 2)

@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(complex=True)
    d = Symbol(complex=True, zero=False)
    Eq << apply(Equal(sqrt(x ** 2 + d) - x, a))

    Eq << ((sqrt(x ** 2 + d) - x) * (sqrt(x ** 2 + d) + x)).this.expand()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Algebra.EqDiv.of.Eq.transplant.apply(Eq[-1])

    Eq << Eq[-1] - Eq[0]

    Eq << Eq[-1] / 2



if __name__ == '__main__':
    run()
# created on 2021-11-09
