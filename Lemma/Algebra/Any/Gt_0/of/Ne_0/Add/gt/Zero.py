from util import *


@apply
def apply(ne_zero, gt_zero, x=None):
    a = ne_zero.of(Unequal[0])
    b, (S[a], c) = gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c > 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(Unequal(a, 0), b ** 2 - 4 * a * c > 0, x=x)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=a > 0)

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[1], cond=Eq[-2].lhs), Bool.Imp_And.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-2].this.rhs.apply(Algebra.Any.Gt_0.of.Gt_0.Add.gt.Zero, x=x)

    Eq << Bool.Imp_And.of.Cond.Imp.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.Gt_0.of.Lt_0.Add.gt.Zero, x=x)




if __name__ == '__main__':
    run()
# created on 2022-04-03
