from util import *

# given: x != y
# x not in {y}


@apply
def apply(inequality_a, inequality_b):
    x, a = inequality_a.of(Unequal)
    _x, b = inequality_b.of(Unequal)

    if x != _x:
        if a == _x:
            x, a = a, x
        elif a == b:
            x, a = a, x
            _x, b = b, _x

        assert x == _x

    return NotElement(x, {a, b})


@prove
def prove(Eq):
    from Lemma import Set
    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, a), Unequal(x, b))

    Eq << Set.NotIn.of.Ne.apply(Eq[0], simplify=False)
    Eq << Set.NotIn.of.Ne.apply(Eq[1], simplify=False)

    Eq << Set.NotIn_Union.of.NotIn.NotIn.apply(Eq[-1], Eq[-2], simplify=False)


if __name__ == '__main__':
    run()

# created on 2018-03-09
