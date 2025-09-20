from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Range)

    if interval.right_open:
        return Less(x, b)
    else:
        if interval.left_open:
            return Less(a, x)


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Set.And.of.In_Range.apply(Eq[0])




if __name__ == '__main__':
    run()

# created on 2021-03-12
# updated on 2023-05-03
del domain
from . import domain
