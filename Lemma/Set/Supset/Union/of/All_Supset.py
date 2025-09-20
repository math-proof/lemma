from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Supset])
    return Supset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)

    Eq << apply(All[i:n](Supset(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << Set.Subset.Cup.of.All_Subset.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-01-15
