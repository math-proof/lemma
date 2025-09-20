from util import *


@apply
def apply(self):
    x, y = self.of(Expr ** 4 + 4 * Expr ** 4)
    return Equal(self, (x ** 2 + 2 * x * y + 2 * y ** 2) * (x ** 2 - 2 * x * y + 2 * y ** 2))


@prove
def prove(Eq):
    x, y = Symbol(complex=True)
    Eq << apply(x ** 4 + 4 * y ** 4)

    Eq << Eq[0].this.rhs.expand()

    # https://en.wikipedia.org/wiki/Sophie_Germain# Memorials


if __name__ == '__main__':
    run()
# created on 2023-04-30

