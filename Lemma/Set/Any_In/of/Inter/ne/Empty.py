from util import *


@apply
def apply(given, wrt=None, index=0):
    [*s] = given.of(Unequal[Intersection, EmptySet])

    A = s.pop(index)
    B = Intersection(*s)

    if wrt is None:
        wrt = B.element_symbol(A.free_symbols)

    return Any[wrt:B](Element(wrt, A))


@prove
def prove(Eq):
    from Lemma import Set, Bool

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A & B, A.etype.emptySet))

    Eq << Set.Eq_Empty.ou.Any_In.apply(A & B)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.In.In.of.In_Inter, simplify=None)

    Eq << Bool.AnySetOf.of.Any_And.apply(Eq[-1], index=1, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-09-07
