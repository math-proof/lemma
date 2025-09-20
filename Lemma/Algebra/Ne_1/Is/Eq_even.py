from util import *


@apply
def apply(self):
    expr = self.of(Unequal[1])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 1))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_even.of.Ne_1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne.given.Eq_0)




if __name__ == '__main__':
    run()
# created on 2023-05-22
