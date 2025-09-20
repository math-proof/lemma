from util import *


@apply
def apply(self):
    function, (n, S[n], (a, b)) = self.of(Sum[Tuple[Equal[Expr % 2, 1], Range]])
    return Equal(self, Sum[n:a // 2:b // 2](function._subs(n, 2 * n + 1)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:Equal(i % 2, 1):Range(a, b)](f[i]))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    S = Symbol(imageset(i, 2 * i + 1, Eq[-1].rhs.limits_cond))
    Eq << S.this.definition

    Eq << Algebra.Sum.eq.Sum_MulBool.apply(Sum[i:S](f[i]))

    Eq << Eq[-1].this.lhs.limits[0][1].definition

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.Imageset)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.find(Element[Symbol, ~Symbol]).definition

    Eq << Eq[-1].this.find(And).apply(Set.Eq_odd.In.Is.In)





if __name__ == '__main__':
    run()

# created on 2018-06-01
# updated on 2023-05-30
