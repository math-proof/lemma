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

    Eq << Eq[1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2020-10-16
# updated on 2022-01-01


