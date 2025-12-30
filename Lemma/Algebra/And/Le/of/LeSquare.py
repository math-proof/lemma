from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return LessEqual(x, sqrt(a)), LessEqual(-sqrt(a), x)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << Algebra.Le_0.of.Le.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Algebra.Or.of.Le_0.split.Mul.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(Algebra.Le.transport, lhs=0)

    Eq << Eq[-1].this.args[0].args[1].apply(Algebra.Ge.transport, lhs=1)

    Eq << Eq[-1].this.args[0].apply(Set.In_Icc.of.Le.Le)

    Eq << Eq[-1].this.args[1].args[0].apply(Algebra.Le.transport, lhs=1)

    Eq << Eq[-1].this.args[1].args[1].apply(Algebra.Ge.transport, lhs=0)

    Eq << Eq[-1].this.args[1].apply(Set.In_Icc.of.Le.Le)

    Eq << Eq[-1].this.rhs.apply(Set.Union.eq.Icc.Abs)

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-06-18
