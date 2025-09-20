from util import *


@apply
def apply(self):
    (x, y), n = self.of(Add ** Expr)
    s = 0
    for k in range(n + 1):
        s += binomial(n, k) * x ** k * y ** (n - k)
    return Equal(self, s)


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    n = 4
    Eq << apply((x + y) ** n)

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2018-08-17
