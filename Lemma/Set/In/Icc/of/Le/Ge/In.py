from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    S[a], S[b] = domain.of(Interval)

    return Element(x, Interval(_a, _b, **domain.kwargs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Interval(a, b, right_open=True)))

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[-1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[2])

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[-2], Eq[0])

    Eq << Algebra.Lt.of.Lt.Ge.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2018-11-05
# updated on 2025-04-10
