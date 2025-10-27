from util import *


@apply
def apply(self):
    ((i, (b, (j, d))), (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true]) = self.of(Piecewise[ExprCondPair[sin[Expr * Expr ** (-Expr / Expr)], Equal[Expr % 2]], ExprCondPair[cos]])
    return Equal(self, sin(S.Pi / 2 * (j % 2) + i / b ** (2 * (j // 2) / d)))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Nat

    n, b = Symbol(positive=True, integer=True)
    d = Symbol(integer=True, positive=True, even=True)
    PE, PE_quote, Z = Symbol(real=True, shape=(n, d))
    i, j = Symbol(integer=True)
    Eq << apply(Piecewise((sin(i / b ** (j / d)), Equal(j % 2, 0)), (cos(i / b ** ((j - 1) / d)), True)))

    Eq << Eq[0].this.rhs.find(Mod).apply(Algebra.Mod.eq.Ite)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Floor).apply(Algebra.Floor.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.distribute, simplify=None)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul.distribute, simplify=None)

    Eq << Eq[-1].this.find(Pow[Piecewise]).apply(Nat.Pow_Ite.eq.Ite_PowS, simplify=None)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)


    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Nat.AddIteS.eq.IteAnd, simplify=None)
    Eq << Eq[-1].this.rhs.apply(Trigonometry.Sin.eq.Ite, simplify=None)



if __name__ == '__main__':
    run()
# created on 2022-01-23
