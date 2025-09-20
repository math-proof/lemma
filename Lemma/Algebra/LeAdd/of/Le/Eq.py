from util import *


@apply
def apply(x_less_than_b, a_less_than_x):
    a, x = a_less_than_x.of(Equal)
    b, y = x_less_than_b.of(LessEqual)

    return LessEqual(a + b, x + y)


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)

    Eq << apply(y <= b, Equal(a, x))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1] - x



if __name__ == '__main__':
    run()
# created on 2021-09-24
