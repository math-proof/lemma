from util import *


@apply
def apply(equal, less_than):
    if not equal.is_Equal:
        equal, less_than = less_than, equal
    x, y = equal.of(Equal)
    a, b = less_than.of(GreaterEqual)
    return LessEqual(x - a, y - b)


@prove
def prove(Eq):
    x, y, a, b = Symbol(real=True)

    Eq << apply(Equal(y, x), a >= b)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - x

    Eq << -Eq[-1]



if __name__ == '__main__':
    run()
# created on 2019-04-26
