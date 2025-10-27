from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, this < arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, y, z = Symbol(real=True)
    Eq << apply(Max(x, y))

    Eq << Eq[0].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].lhs.this.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].subs(x, z)

    Eq << Eq[-1].subs(y, x)
    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    run()
# created on 2019-06-18
