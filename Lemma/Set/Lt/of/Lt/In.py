from util import *


@apply
def apply(lt, contains_y):
    y, domain_y = contains_y.of(Element)
    a, b = domain_y.of(Interval)
    x, S[y] = lt.of(Less)
    return x < b


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(x < y, Element(y, Interval(a, b)))

    Eq << Set.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-25

