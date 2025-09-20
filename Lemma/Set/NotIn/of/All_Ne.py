from util import *


@apply
def apply(given):
    (x, y), (lhs, *rhs) = given.of(All[Unequal])
    if len(rhs) == 2:
        rhs = lhs.range(*rhs)
    else:
        rhs, = rhs

    if x == lhs:
        return NotElement(y, rhs)
    if y == lhs:
        return NotElement(x, rhs)


@prove
def prove(Eq):
    from Lemma import Set
    i = Symbol(integer=True)
    j = Symbol(integer=True, given=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(i, j)))

    Eq << ~Eq[-1]
    Eq << Set.Any.Eq.of.In.apply(Eq[-1], reverse=True)
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-01-15

