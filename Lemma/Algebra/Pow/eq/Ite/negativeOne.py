from util import *


@apply
def apply(self):
    n = self.of((-1) ** Expr)
    assert n.is_integer
    return Equal(self, Piecewise((1, Equal(n % 2, 0)), (-1, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    n = Symbol(integer=True)
    Eq << apply((-1) ** n)

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[1].this.find(Equal & ~Equal).apply(Algebra.Eq_even.Is.Eq)

    Eq << Eq[-1].this.find(Unequal).apply(Algebra.Ne_0.Is.Eq_odd)

    Eq << Eq[-1].this.find(Equal & ~Equal).apply(Algebra.Eq_odd.Is.Eq)

    Eq << Set.PowNeg1.In.Finset.apply((-1) ** n)

    Eq << Set.Or.Eq.of.In_Finset.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2020-03-01
# updated on 2023-04-30
