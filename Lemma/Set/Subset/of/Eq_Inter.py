from util import *


@apply
def apply(given):
    (A, B), _A = given.of(Equal[Intersection])
    if _A != A:
        A, B = B, A
    assert _A == A

    return Subset(A, B)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(A & B, A))

    Eq << Set.Subset.given.Eq.Inter.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-11-21
