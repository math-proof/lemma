from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    if x.is_integer:
        S[a], S[b] = domain.of(Range)
        cls = Range
    else:
        S[a], S[b] = domain.of(Interval)
        cls = Interval

    return Element(x, cls(_a, _b, **domain.kwargs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Interval(a, b, right_open=True)))

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[2])

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[-2], Eq[0])

    Eq << Algebra.Lt.of.Lt.Ge.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2018-11-05
# updated on 2025-04-10
