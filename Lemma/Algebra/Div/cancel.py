from util import *


@apply(simplify=False)
def apply(self, factor=None):
    num, den = self.of(Expr / Expr)
    if factor is None:
        if factor := num.find((~Expr) ** -1):
            ...
        else:
            factor = den.find((~Expr) ** -1)
    else:
        factor = sympify(factor)

    assert factor.is_nonzero

    num *= factor
    den *= factor
    num = num.expand()
    den = den.expand()
    return Equal(self, num / den, evaluate=False)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    c, d = Symbol(real=True, zero=False)
    Eq << apply((a + 1 / c) / (b + 1 / d), c * d)

    Eq << Eq[-1].this.lhs.ratsimp()

    
    


if __name__ == '__main__':
    run()
# created on 2020-06-29
# updated on 2023-04-05
