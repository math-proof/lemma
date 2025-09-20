from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Range)
    a = Max(a, _a + 1)
    return Element(y, Range(a, b, right_open=domain.right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x > c, Element(x, Range(a, b)))

    Eq << Set.In_Range.given.And.apply(Eq[2])

    Eq << Set.And.of.In_Range.apply(Eq[1])

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[0])

    Eq << Algebra.GeMax.of.Ge.Ge.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-11-12
