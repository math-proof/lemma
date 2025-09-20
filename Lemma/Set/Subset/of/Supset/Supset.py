from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    X, A = a_less_than_x.of(Supset)
    B, _X = x_less_than_b.of(Supset)
    if X != _X:
        A, X, S[X], B = _X, B, A, X
    return Supset(B, A)


@prove
def prove(Eq):
    from Lemma import Set
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Supset(X, A), Supset(B, X))

    Eq << Eq[1].reversed

    Eq << Set.Subset.of.Subset.Supset.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2021-07-07

