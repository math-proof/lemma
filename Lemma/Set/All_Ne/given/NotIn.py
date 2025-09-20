from util import *


@apply
def apply(imply):
    (x, y), (lhs, *rhs) = imply.of(All[Unequal])
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
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:n](Unequal(i, j)))

    Eq << Set.All.Ne.of.NotIn.apply(Eq[1], reverse=True)


if __name__ == '__main__':
    run()

# created on 2021-01-14
