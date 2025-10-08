from util import *


@apply
def apply(self):
    arg, *args = self.of(Min)
    this = self.func(*args)
    rhs = Piecewise((arg, this > arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z = Symbol(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[0].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].lhs.this.apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].subs(x, z)
    Eq << Eq[-1].subs(y, x)
    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    run()
# created on 2018-08-30
