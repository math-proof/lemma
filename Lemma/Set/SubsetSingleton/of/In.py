from util import *


# given: A in B
# => {A} subset B
@apply(simplify=False)
def apply(given):
    e, s = given.of(Element)

    return subset.Subset(e.set, s)


@prove
def prove(Eq):
    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    contains = Element(e, s, evaluate=False)

    Eq << apply(contains)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-03-30
