from util import *


@apply
def apply(self, mid):
    expr, (x, n) = self.of(Difference)
    assert mid >= 0, "mid >= 0 => %s" % (mid >= 0)
    assert mid <= n, "mid <= n => %s" % (mid <= n)

    rhs = Difference(Difference(expr, (x, mid)).simplify(), (x, n - mid))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    x = Symbol(real=True)
    f = Function(real=True)
    d = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Difference(f(x), (x, d)), d - 1)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-10-08
