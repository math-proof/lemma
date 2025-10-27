from util import *


@apply
def apply(self):
    *z, max_xy = self.of(Expr + Max)
    z = Add(*z)

    args = [e + z for e in max_xy]

    return Equal(self, Max(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x, y, z = Symbol(real=True)
    Eq << apply(Max(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.rhs.apply(Nat.Ite.eq.SubIte)

    Eq << Eq[-1].this.lhs.apply(Nat.Max.eq.IteGe)


if __name__ == '__main__':
    run()
# created on 2018-08-06
