from util import *


@apply
def apply(lt_zero, *, cond=None):
    a = lt_zero.of(Expr < 0)
    assert cond.is_Inequality
    lhs, rhs = cond.args
    lhs /= a
    lhs = lhs.ratsimp()
    rhs /= a
    rhs = rhs.ratsimp()
    return Iff(cond, cond.reversed_type(lhs, rhs, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Bool, Nat, Rat, Int

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, cond= a * x + b < 0)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[1])

    Eq <<= Bool.And_Imp.given.And_ImpAnd.apply(Eq[0], Eq[-2]), Bool.And_Imp.given.And_ImpAnd.apply(Eq[0], Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Rat.GtDiv.of.Lt_0.Lt)

    Eq << Eq[-1].this.lhs.apply(Int.LtMul.of.Lt_0.Gt)

    Eq << Eq[-1].this.lhs.lhs.apply(Nat.Mul_Add.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2023-04-11
