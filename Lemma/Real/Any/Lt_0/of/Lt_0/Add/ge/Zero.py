from util import *


@apply
def apply(lt_zero, add_ge_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = add_ge_zero.of(Expr ** 2 - Expr * Expr * 4 >= 0)
    assert x.is_real and not x.is_given
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from Lemma import Set, Bool, Nat, Int, Rat, Real

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c >= 0, x=x)

    Eq.delta_is_nonnegative = Real.GeSqrt_0.of.Ge_0.apply(Eq[1])

    Eq << Eq.delta_is_nonnegative - b

    Eq << Rat.LeDivS.of.Ge.Lt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] / 2

    Eq << Set.In_Iic.of.Le.apply(Eq[-1])

    Eq << Set.In_Union.of.In.apply(Eq[-1], Reals, simplify=None)

    epsilon = Symbol(negative=True)
    Eq << Set.InAdd.of.In_Icc.apply(Eq[-1], epsilon, simplify=None)

    Eq << Bool.Any_UFn.given.UFnUFn.apply(Eq[2], x, Eq[-1].lhs)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Add ** 2).apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Expr ** 2).apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)

    Eq << Eq[-1].this.lhs.apply(Int.AddAddS.eq.MulAddS)

    Eq << Eq[-1].this.find(Symbol * Add).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Symbol * Add).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1] / epsilon

    Eq << Eq[-1].this.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[0] * epsilon

    Eq << Nat.Add.gt.Zero.of.Gt_0.Ge_0.apply(Eq[-1], Eq.delta_is_nonnegative)




if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2023-05-15
