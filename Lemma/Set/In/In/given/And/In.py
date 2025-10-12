from util import *


@apply
def apply(el_c, el_x, start=True, stop=False):
    c, s0 = el_c.of(Element)
    x, s = el_x.of(Element)

    assert s0 in s

    assert s.is_Range or s.is_Interval
    if stop:
        s = s.copy(stop=c)
    elif start:
        s = s.copy(start=c)
    return el_c, Element(x, s)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    a, b, c, x = Symbol(real=True)
    Eq << apply(Element(c, Interval.open(a, b)), Element(x, Interval(a, b)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[-1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Gt.of.Ge.Gt.apply(Eq[-4], Eq[-2])

    Eq << Nat.Ge.of.Gt.apply(Eq[-1])

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-10-15
