from util import *


@apply
def apply(given, self):
    a = given.of(Equal[Expr % 2, 0])
    expr, (i, rgn) = self.of(Sum)
    S[a], b, S[2] = rgn.of(Range)

    return Equal(self, Sum[i:a // 2:(b + 1) // 2](expr._subs(i, 2 * i)))


@prove
def prove(Eq):
    from Lemma import Finset, Int

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(a % 2, 0), Sum[i:Range(a, b, 2)](f[i]))

    Eq << Eq[1].lhs.this.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(Element).apply(Int.In_Range.Is.Mod.In_Range)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_MulBoolAnd.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Finset.SumSetOf_Even.eq.Sum_UFnMul2)

    Eq << Int.Div_2.of.Even.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2023-05-30
