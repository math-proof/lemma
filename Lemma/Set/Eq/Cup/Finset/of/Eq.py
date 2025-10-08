from util import *


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)
    lhs, rhs = Cup(lhs.set, *limits), Cup(rhs.set, *limits)
    if simplify:
        lhs, rhs = lhs.simplify(), rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Bool.All.of.Cond.apply(Eq[0], i)

    Eq << Set.Eq.Cup.Finset.of.All_Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-24
