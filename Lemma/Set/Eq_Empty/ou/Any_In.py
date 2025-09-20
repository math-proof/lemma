from util import *



@apply
def apply(S):
    assert S.is_set

    e = S.element_symbol()
    return Any(Element(e, S), (e,)) | Equal(S, e.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    S = Symbol(etype=dtype.real)

    Eq << apply(S)

    Eq << Eq[-1].apply(Logic.All.given.All.AllNot, cond=Unequal(S, S.etype.emptySet))

    Eq << Eq[-1].this.expr.apply(Set.Any_In.given.Ne_Empty)


if __name__ == '__main__':
    run()

# created on 2018-09-06
