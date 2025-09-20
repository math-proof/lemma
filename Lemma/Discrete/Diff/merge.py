from util import *


@apply
def apply(self):
    (expr, (x, d)), (S[x], n) = self.of(Difference[Difference])
    return Equal(self, Difference(expr, (x, n + d)), evaluate=False)


@prove
def prove(Eq):
    x = Symbol(real=True)
    f = Function(real=True)
    d, n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Difference(Difference(f(x), (x, d)), (x, n - d)))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-10-12
