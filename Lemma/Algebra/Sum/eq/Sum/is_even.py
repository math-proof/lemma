from util import *


@apply
def apply(self):
    function, (n, S[n], (a, b)) = self.of(Sum[Tuple[Equal[Expr % 2, 0], Range]])
    return Equal(self, Sum[n:(a + 1) // 2:(b + 1) // 2](function._subs(n, 2 * n)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    n, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[n:Equal(n % 2, 0):Range(a, b)](f[n]))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    S = Symbol(imageset(n, 2 * n, Eq[-1].rhs.limits_cond))
    Eq << S.this.definition

    Eq << Algebra.Sum.eq.Sum_MulBool.apply(Sum[n:S](f[n]))

    Eq << Eq[-1].this.lhs.limits[0][1].definition

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.Imageset)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.args[1].arg.rhs.definition

    Eq << Eq[-1].this.find(And).apply(Set.Eq_even.In.Is.In)

    Eq << Eq[-1].this.find(Floor + 1).apply(Algebra.Add.eq.Floor)



if __name__ == '__main__':
    run()

# created on 2018-05-28
# updated on 2023-05-30
