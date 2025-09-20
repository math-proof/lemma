from util import *


@apply
def apply(self):
    (x, d), S[d] = self.of(Floor[Expr / Expr] * Expr)
    assert d.is_integer and x.is_integer
    return Equal(self, x - x % d)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, d = Symbol(integer=True)
    Eq << apply(x // d * d)

    Eq << Algebra.Mod.eq.Sub_Mul_Div.apply(x % d)

    Eq << Eq[0] - Eq[1]


if __name__ == '__main__':
    run()
# created on 2020-01-28
