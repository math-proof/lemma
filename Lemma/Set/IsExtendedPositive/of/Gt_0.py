from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Element(x, Interval(0, oo, left_open=True, right_open=False))


@prove
def prove(Eq):
    x = Symbol(hyper_real=True)
    Eq << apply(x > 0)

    Eq << Eq[1].simplify()


if __name__ == '__main__':
    run()
# created on 2020-04-24
