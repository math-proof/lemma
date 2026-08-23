from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Equal)
    b, y = x_less_than_b.of(Greater)

    return Greater(a + b, x + y)


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)

    Eq << apply(Equal(a, x), y > b)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - x



if __name__ == '__main__':
    run()
# created on 2021-08-12
