from util import *


def take_sqrt(x):
    if x.is_Pow:
        b, e = x.args
        if e.is_integer and e.is_even:
            return b ** (e / 2)

    return sqrt(x)

@apply
def apply(self):
    x, y = self.of(Expr - Expr)

    x = take_sqrt(x)

    y = take_sqrt(y)

    return Equal(self, (x - y) * (x + y))


@prove
def prove(Eq):
    x, y = Symbol(complex=True)
    Eq << apply(x * x - y * y)

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-06-25
