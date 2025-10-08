from util import *


@apply
def apply(given, index=-1):
    function, *limits = given.of(All)

    assert len(limits) > 1
    del limits[index]

    return All(function, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(integer=True)

    A, B = Symbol(etype=dtype.integer)

    f = Function(integer=True)

    Eq << apply(All[x:A, y:B](f(x, y) > 0))

    Eq << ~Eq[0]

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-06
