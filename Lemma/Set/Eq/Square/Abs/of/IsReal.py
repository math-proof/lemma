from util import *


@apply
def apply(given, reverse=False):
    x, R = given.of(Element)
    assert R in Reals
    if reverse:
        return Equal(x ** 2, abs(x) ** 2)
    return Equal(abs(x) ** 2, x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(-oo, oo)))

    Eq << Eq[1].this.lhs.apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Set.EqConj.of.IsReal.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-26
# updated on 2023-06-27
