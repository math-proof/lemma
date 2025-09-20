from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Equal[EmptySet])

    A, B = AB.of(Intersection)
    if wrt is None:
        wrt = given.generate_var(**A.etype.dict)

    return All[wrt:A](NotElement(wrt, B))


@prove
def prove(Eq):
    from Lemma import Set
    B, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(A & B, A.emptySet))

    Eq << ~Eq[1]

    Eq << Set.Any_And_In.of.Any.apply(Eq[-1])

    Eq << Set.Ne_Empty.of.Any_In.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-05-12
