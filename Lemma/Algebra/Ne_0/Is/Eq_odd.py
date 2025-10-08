from util import *



@apply
def apply(self):
    expr = self.of(Unequal[0])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_odd.of.Ne_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.given.Eq_odd)

if __name__ == '__main__':
    run()
# created on 2020-01-27
