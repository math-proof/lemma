from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return Element(x, Interval.open(-sqrt(a), sqrt(a)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Int

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 < a ** 2)

    Eq << Eq[0].this.rhs.apply(Set.In_Icc.Is.And)

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Int.And.Lt.of.LtSquare)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtSquare.given.And.Lt)


if __name__ == '__main__':
    run()
# created on 2023-06-18
