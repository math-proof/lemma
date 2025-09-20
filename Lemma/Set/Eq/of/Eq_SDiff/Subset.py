from util import *


@apply
def apply(subset, equal):
    C, A = subset.of(Subset)

    complement_A_C, complement_B_C = equal.of(Equal)
    _A, S[C] = complement_A_C.of(Complement)
    B, S[C] = complement_B_C.of(Complement)

    if A != _A:
        S[A], B = B, _A

    return Equal(A, B | C)


@prove
def prove(Eq):
    from Lemma import Set
    A, B, C = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(C, A), Equal(A - C, B - C))

    Eq << Set.EqUnionS.of.Eq.apply(Eq[1], C)

    Eq << Set.EqUnion.of.Subset.apply(Eq[0])

    Eq << Eq[-2].this.lhs.subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-31
