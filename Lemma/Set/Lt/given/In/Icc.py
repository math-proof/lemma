from util import *

# given: |A| >= 1
# A != {}


@apply(simplify=False)
def apply(given):
    n, b = given.of(Less)

    return Element(n, Interval.open(-oo, b))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)

    Eq << apply(n < b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2020-04-09
