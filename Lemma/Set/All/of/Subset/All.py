from util import *


@apply
def apply(subset, forall):
    function, *limits = forall.of(All)

    B, A = subset.of(Subset)

    for index, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == A:
                break
        elif len(domain) == 2:
            if x.range(*domain) == A:
                break
    else:
        return

    assert index >= 0
    limits[index] = (x, B)
    return All(function, *limits)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n])
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=())
    Eq << apply(Subset(B, A), All[x:A](Equal(f(x), 1)))

    Eq << Set.All_In.of.Subset.apply(Eq[0], wrt=x)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[1])

    Eq << Logic.Imp.of.Imp.Imp.apply(Eq[-1], Eq[-2])

    Eq << Logic.All.given.Imp.apply(Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-04-01
