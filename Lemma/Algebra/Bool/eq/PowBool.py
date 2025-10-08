from util import *


@apply
def apply(self, n=None):
    assert self.is_Bool
    assert n.is_integer
    assert n > 0
    return Equal(self, self ** n)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(real=True)

    n = Symbol(integer=True, positive=True, given=False)

    Eq << apply(functions.Bool(x > y), n)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq[0] * functions.Bool(x > y)

    Eq << Eq[-1].this.lhs.apply(Algebra.SquareBool.eq.Bool)

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

if __name__ == '__main__':
    run()

# created on 2019-03-06
