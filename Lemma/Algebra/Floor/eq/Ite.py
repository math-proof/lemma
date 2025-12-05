from util import *


@apply
def apply(self):
    n, S[2] = self.of(Floor[Expr / Expr])
    assert n.is_integer
    return Equal(self, Piecewise((n / 2, Equal(n % 2, 0)), ((n - 1) / 2, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    n = Symbol(integer=True)
    Eq << apply(n // 2)

    Eq << Eq[0].this.lhs.apply(Algebra.Floor.eq.Mul.Div)

    Eq << Eq[-1].this.rhs.apply(Nat.Ite.eq.SubIte)

    Eq << Eq[-1] * -2

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS, simplify=None)

    Eq << Algebra.Mod.eq.Ite.apply(Eq[-1].lhs)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2022-01-23
