from util import *


@apply(simplify=False)
def apply(given):
    x, y = given.of(Equal)

    return Equal(x - y, Zeros(*x.shape))


@prove
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, zero=False)
    Eq << apply(Equal(a, b))

    Eq << Eq[1] + b

    


if __name__ == '__main__':
    run()
# created on 2018-05-09
# updated on 2022-07-02
