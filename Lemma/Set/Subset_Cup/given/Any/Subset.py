from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Subset)
    function, *limits = rhs.of(Cup)
    return Any(Subset(lhs, function).simplify(), *limits)


@prove
def prove(Eq):
    from Lemma import Set

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])
    Eq << apply(Subset(A, Cup[i:n](x[i])))

    Eq << Set.Subset.Cup.of.Any_Subset.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-06-01
