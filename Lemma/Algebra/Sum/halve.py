from util import *


@apply
def apply(self, *, simplify=True):
    expr, (i, rgn) = self.of(Sum)
    a, b, S[2] = rgn.of(Range)
    rhs = Sum[i:a // 2:(b + (a + 1) % 2) // 2](expr._subs(i, 2 * i + a % 2))
    if simplify:
        rhs = rhs.simplify()
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:Range(a, b, 2)](f[i]))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(a % 2, 0))

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_odd.of.Ne_0)

    Eq <<= Logic.Imp.given.ImpEq.apply(Eq[-3]), Logic.Imp.given.ImpEq.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Eq_odd.of.Eq_even, ret=0), Eq[-1].this.lhs.apply(Algebra.Eq_even.of.Eq_odd, ret=0)

    Eq <<= Logic.Imp_And.given.Imp.And.subst.apply(Eq[-2], 1), Logic.Imp_And.given.Imp.And.subst.apply(Eq[-1], 1)

    Eq <<= Logic.Imp_And.given.Imp.delete.apply(Eq[-2]), Logic.Imp_And.given.Imp.delete.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.EqSum.of.Eq_even, Eq[0].lhs)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqSum.of.Eq_odd, Eq[0].lhs)




if __name__ == '__main__':
    run()
# created on 2023-05-30
