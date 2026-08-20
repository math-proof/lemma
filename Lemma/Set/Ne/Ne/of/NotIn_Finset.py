from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(NotElement[FiniteSet])

    lhs = FiniteSet(*args[:index])
    rhs = FiniteSet(*args[index:])

    return NotElement(e, lhs).simplify(), NotElement(e, rhs).simplify()


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True)
    Eq << apply(NotElement(x, {a, b}))



    Eq << Set.Ne.of.NotIn.apply(Eq[0])

    Eq << Set.Ne.of.NotIn.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()

# created on 2018-11-17
