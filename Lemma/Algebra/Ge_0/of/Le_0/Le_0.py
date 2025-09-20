from util import *


@apply
def apply(is_nonpositive_x, is_nonpositive_y):
    x = is_nonpositive_x.of(Expr <= 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x <= 0, y <= 0)

    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(-Eq[0], -Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-09-02
