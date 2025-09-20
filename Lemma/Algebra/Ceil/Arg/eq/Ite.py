from util import *


@apply
def apply(self):
    ((AB, S[3 / (S.Pi * 2)]), S[S.One  / 2]) = self.of(Ceil[Arg * Expr - Expr])
    delta_0, delta_1 = AB.of(Expr ** (S.One / 3) * Expr ** (S.One / 3))

    q = (delta_0 + delta_1) / -2

    delta = (delta_1 - delta_0) / 2
    delta **= 2

    p3 = (delta - q ** 2) * 27 / 4
    p = p3.of(Expr ** 3)
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    return Equal(self, Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p, q = Symbol(complex=True, given=True)
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q
    Eq << apply(Ceil(3 * Arg(U ** (S.One / 3) * V ** (S.One / 3)) / (S.Pi * 2) - S.One / 2))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(p, 0))

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-2])

    Eq << Algebra.Mul.Root.eq.Mul.Ite.cubic_root.apply(Eq[-1].find(Arg[~Mul]))

    Eq << Eq[-1].this.find(Pow[~Mul]).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Unequal(p, 0).this.apply(Algebra.Ceil_Arg.eq.Ite.of.Ne_0, q)

    Eq << Eq[-1].lhs.this.apply(Logic.Iff.Eq.of.Ne_0, Eq[-1].find(Equal[~Ceil, 0]))

    Eq <<= Eq[-1] & Eq[-2]
    Eq << Eq[-1].this.rhs.apply(Logic.Cond.of.Iff.Cond.subst)



if __name__ == '__main__':
    run()
# created on 2018-11-09
