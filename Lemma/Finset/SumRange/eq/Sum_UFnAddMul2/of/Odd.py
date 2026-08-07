from util import *


@apply
def apply(given, self):
    a = given.of(Equal[Expr % 2, 1])
    expr, (i, rgn) = self.of(Sum)
    S[a], b, S[2] = rgn.of(Range)

    return Equal(self, Sum[i:a // 2:b // 2](expr._subs(i, 2 * i + 1)))


@prove
def prove(Eq):
    from Lemma import Set, Finset

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(a % 2, 1), Sum[i:Range(a, b, 2)](f[i]))

    Eq << Eq[1].lhs.this.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Range.Is.Mod.In_Range)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_MulBoolAnd.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Finset.SumSetOf_Odd.eq.Sum_UFnAddMul2)


if __name__ == '__main__':
    run()
# created on 2023-05-30
