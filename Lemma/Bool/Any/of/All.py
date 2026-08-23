from util import *


@apply
def apply(given):
    expr, *limits = given.of(All)
    assert Tuple.is_nonemptyset(limits)
    return Any(expr, *limits)


@prove
def prove(Eq):
    from Lemma import Set

    S = Range(oo)
    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(All[e:S](f(e) > 0))

    Eq << Unequal(S, S.etype.emptySet, plausible=True)

    Eq << Set.Any.of.All.Ne_Empty.apply(Eq[-1], Eq[0])




if __name__ == '__main__':
    run()

# created on 2018-12-18
# updated on 2023-11-10
