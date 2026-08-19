from util import *


@apply
def apply(ne, self):
    λ = ne.of(Unequal[1])
    (S[λ], k), (S[k], S[0], n) = self.of(Sum[Pow])
    return Equal(self, (1 - λ ** n) / (1 - λ), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Finset, Fin, Real

    k, n = Symbol(integer=True)
    λ = Symbol(real=True)
    Eq << apply(Unequal(λ, 1), Sum[k:n](λ ** k))

    Eq << (λ ** (k + 1)).this.apply(Real.Pow_Add.eq.MulPowS.of.Gt_0)

    Eq << Eq[-1] - λ ** k

    Eq << -Eq[-1].reversed

    Eq << Eq[-1].this.lhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << -Algebra.Ne_0.of.Ne.apply(Eq[0])

    Eq << Nat.Div.of.Eq.Ne_0.apply(Eq[-1], Eq[-2])

    Eq << Fin.Sum.of.All_Eq.apply(Eq[-1], (k, 0, n))

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum[Pow[Add]]).apply(Finset.SumIco.eq.Sum_UFnAdd, -1)



if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-04-15
