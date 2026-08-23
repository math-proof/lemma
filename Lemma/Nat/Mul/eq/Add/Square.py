from util import *


@apply
def apply(self):
    (z, x), (S[z], y) = self.of(Mul[Expr - Expr, Expr - Expr])
    return Equal(self, ((z - x) ** 2 + (z - y) ** 2 - (x - y) ** 2) / 2)


@prove
def prove(Eq):

    x, y, z = Symbol(complex=True)

    Eq << apply((z - x) * (z - y))

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-11-03
