from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return LessEqual(x, sqrt(a)), LessEqual(-sqrt(a), x)


@prove
def prove(Eq):
    from Lemma import Set, Nat, Bool, Int

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << Nat.Le_0.of.Le.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Int.Sub.Square.eq.Mul)

    Eq << Bool.Or.of.Le_0.split.Mul.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(Nat.Le.transport, lhs=0)

    Eq << Eq[-1].this.args[0].args[1].apply(Nat.Ge.transport, lhs=1)

    Eq << Eq[-1].this.args[0].apply(Set.In_Icc.of.Le.Le)

    Eq << Eq[-1].this.args[1].args[0].apply(Nat.Le.transport, lhs=1)

    Eq << Eq[-1].this.args[1].args[1].apply(Nat.Ge.transport, lhs=0)

    Eq << Eq[-1].this.args[1].apply(Set.In_Icc.of.Le.Le)

    Eq << Eq[-1].this.rhs.apply(Set.Union.eq.Icc.Abs)

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-06-18
