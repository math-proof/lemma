from util import *


@apply
def apply(given):
    return Equal(*given.of(Unequal[KroneckerDelta, 0]))


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Unequal(KroneckerDelta(a, b), 0))

    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()
# created on 2020-09-05
