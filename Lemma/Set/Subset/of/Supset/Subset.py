from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    X, A = a_less_than_x.of(Supset)
    _X, B = x_less_than_b.of(Subset)
    if X != _X:
        A, X, S[X], B = _X, B, A, X
    return Subset(A, B)


@prove
def prove(Eq):
    from Lemma import Set
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Supset(X, A), Subset(X, B))

    Eq << Eq[0].reversed

    Eq << Set.Subset.of.Subset.Subset.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-07-06

