from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return Element(x, Interval(-sqrt(a), sqrt(a)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << Eq[0].this.rhs.apply(Set.In_Icc.Is.And)

    Eq << Eq[-1].this.find(GreaterEqual).reversed

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.Le.of.LeSquare)

    Eq << Eq[-1].this.rhs.apply(Algebra.LeSquare.given.And.Le)




if __name__ == '__main__':
    run()
# created on 2023-06-18
