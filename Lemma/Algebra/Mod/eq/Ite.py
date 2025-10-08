from util import *


@apply
def apply(self):
    n, S[2] = self.of(Expr % Expr)
    assert n.is_integer
    return Equal(self, Piecewise((0, Equal(n % 2, 0)), (1, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(integer=True)
    Eq << apply(n % 2)

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Set.Or.given.In.Finset.apply(Eq[-1])

    Eq << Set.Mod.In.Ico.apply(Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Set.Ico.eq.Finset)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2023-04-30
