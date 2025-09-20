from util import *


@apply
def apply(le, contains_y):
    y, a = le.of(LessEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Range)
    a = Min(c, a + 1)
    return Element(y, Range(b, a, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x <= a, Element(x, Range(b, c)))

    Eq << Set.In_Range.given.And.apply(Eq[2])

    Eq << Set.And.of.In_Range.apply(Eq[1])

    Eq << Algebra.Lt.of.Le.relax.apply(Eq[0])
    Eq << Algebra.LtMin.of.Lt.Lt.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-11-12
