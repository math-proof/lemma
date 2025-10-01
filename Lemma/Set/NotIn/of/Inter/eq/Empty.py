from util import *


# given A & B = {} => A - B = A
@apply
def apply(given):
    A, B = given.of(Equal[Intersection, EmptySet])
    if A.is_FiniteSet:
        if len(A) != 1:
            swap = True
        else:
            swap = False
    else:
        swap = True
    if swap:
        A, B = B, A

    a = A.of(FiniteSet)

    return NotElement(a, B)


@prove
def prove(Eq):
    from Lemma import Set
    a = Symbol(integer=True, given=True)
    B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(a.set & B, a.emptySet))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(Set.EqUnion.of.In)

    Eq << Eq[-1].apply(Set.EqInter.of.Eq, a.set)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-09-08
