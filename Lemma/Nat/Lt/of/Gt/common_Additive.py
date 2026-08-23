from util import *


@apply
def apply(given, t, alpha):
    x, y = given.of(Norm[Expr - Expr] > 0)
    assert x.shape == y.shape == t.shape
    assert alpha > 0

    x_quote = Symbol("x'", (x + t * alpha) / (1 + alpha))
    y_quote = Symbol("y'", (y + t * alpha) / (1 + alpha))
    return Less(Norm(x_quote - y_quote), Norm(x - y))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, t = Symbol(real=True, shape=(n,))
    alpha = Symbol(real=True, positive=True)
    Eq << apply(Norm(x - y) > 0, t, alpha)

    Eq << Eq[-1].this.lhs.arg.args[0].definition

    Eq << Eq[-1].this.lhs.arg.args[0].args[1].definition

    Eq << Eq[-1].this.lhs.arg.ratsimp()

    Eq << Eq[-1] * (1 + alpha)

    Eq << Eq[-1] - Eq[-1].lhs

    Eq << Eq[-1].this.rhs.collect(Norm(x - y)).reversed

    Eq << Eq[0] * alpha


if __name__ == '__main__':
    run()

# created on 2021-09-23
