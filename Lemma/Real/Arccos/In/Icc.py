from util import *


@apply(simplify=False)
def apply(x):
    return Element(acos(x), Interval(0, S.Pi))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-30
