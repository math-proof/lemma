from util import *

# given: A != {}
# Any[x] (x in A)


@apply
def apply(given):
    A, B = given.of(Unequal)
    if B:
        assert not A
        A = B
    x = A.element_symbol()
    return Any[x](Element(x, A))


@prove
def prove(Eq):
    from Lemma import Set

    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq << Set.Eq_Empty.of.All_NotIn.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()


# created on 2018-03-06
