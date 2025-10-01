from util import *


@apply
def apply(ge, contains_y):
    y, a = ge.of(GreaterEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Range)
    a = Max(b, a)
    return Element(y, Range(a, c, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x >= a, Element(x, Range(b, c)))

    Eq << Set.In_Ico.given.And.apply(Eq[2])

    Eq << Set.And.of.In_Ico.apply(Eq[1])

    Eq << Algebra.GeMax.of.Ge.Ge.apply(Eq[-1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-11-12
