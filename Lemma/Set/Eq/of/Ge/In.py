from util import *


@apply
def apply(ge, el):
    a, b = ge.of(GreaterEqual)
    x, domain = el.of(Element)
    S[a], S[b] = domain.of(Interval)
    assert not domain.left_open and not domain.right_open
    return Equal(x, a)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(a >= b, Element(x, Interval(a, b)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.Le.of.Ge.Le.apply(Eq[-1], Eq[-2])

    Eq << Nat.Eq.of.Ge.Le.apply(Eq[-1], Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].simplify()




if __name__ == '__main__':
    run()
# created on 2023-10-03
