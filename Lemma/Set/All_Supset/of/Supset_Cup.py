from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Supset)
    expr, *limits = rhs.of(Cup)
    return All(Supset(lhs, expr, ).simplify(), *limits)

@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])

    Eq << apply(Supset(A, Cup[i:n](x[i])))

    Eq << Eq[0].reversed

    Eq << Set.All_Subset.of.Subset_Cup.apply(Eq[-1])

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

# created on 2020-08-11
