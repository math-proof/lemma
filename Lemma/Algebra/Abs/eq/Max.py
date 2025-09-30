from util import *


@apply
def apply(self):
    x = self.of(Abs)
    assert x.is_extended_real
    return Equal(self, Max(x, -x))


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Eq[0].this.lhs.apply(Algebra.Abs.eq.IteGe_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.IteGe)

    Eq << Eq[-1].this.find(Expr >= -Expr).apply(Algebra.Ge.Is.Ge_0)

    Eq << Eq[-1].this.find(Expr * 2 >= 0) / 2


if __name__ == '__main__':
    run()
# created on 2023-06-18
