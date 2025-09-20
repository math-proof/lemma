from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Unequal[EmptySet])

    A, B = AB.of(Complement)
    if wrt is None:
        wrt = A.element_symbol(B.free_symbols)
    assert wrt.type == B.etype
    return Any[wrt:A](Element(wrt, AB))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A - B, A.etype.emptySet))

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Imply(Element(i, A - B), And(Element(i, A - B), Element(i, A)), plausible=True)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.In.of.In_SDiff)

    Eq << Eq[2].this.expr.apply(Logic.Cond.of.Imp.Cond, Eq[-2], simplify=None)

    Eq << Eq[-1].apply(Logic.AnySetOf.of.Any_And, index=0, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-03-24
