from util import *


@apply
def apply(lt, contains_y):
    y, _b = lt.of(Less)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Range)
    b = Min(b, _b)
    return Element(y, Range(a, b, left_open=domain.left_open, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c, x = Symbol(integer=True)
    Eq << apply(x < c, Element(x, Range(a, b)))

    Eq << Set.In_Ico.given.And.apply(Eq[2])

    Eq << Set.Ge.Le_Sub_1.of.In_Ico.apply(Eq[1])

    Eq << Algebra.LtMin.of.Lt.Lt.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-11-12
