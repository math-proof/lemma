from util import *


@apply
def apply(lt_zero, add_lt_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = add_lt_zero.of(Expr ** 2 - Expr * Expr * 4 < 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return a * x ** 2 + b * x + c < 0


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c < 0, x=x)

    Eq << Set.IsNegative.of.Lt_0.apply(Eq[0], simplify=None)

    Eq.a_reciprocal_is_negative = Set.IsNegative.Div.of.IsNegative.apply(Eq[-1])

    t = Symbol(x + Eq.a_reciprocal_is_negative.lhs * b / 2)
    Eq << t.this.definition

    Eq << Algebra.Eq.of.Eq.transport.apply(Eq[-1], rhs=1)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Expr ** 2).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Algebra.Gt_0.of.Lt_0.Lt_0.apply(Eq.a_reciprocal_is_negative, Eq[1])

    Eq << -Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS) / 4

    Eq << GreaterEqual(t ** 2, 0, plausible=True)

    Eq << Algebra.Le_0.of.Lt_0.Ge_0.apply(Eq[0], Eq[-1])

    Eq << Algebra.Lt_0.Add.of.Le_0.Lt_0.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()
# created on 2022-04-02
