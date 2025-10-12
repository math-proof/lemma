from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    if not n >= 0:
        print(__file__, 'warning, not proved!')

    if not k > 0:
        print(__file__, 'warning, not proved!')
    return Equal(self, n / k * Binomial(n - 1, k - 1))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Bool, Nat, Nat

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(binomial(n, k))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(n, 0))

    Eq << Eq[-2].this.apply(Bool.IffImpSAndEq)

    Eq << Eq[-1].this.lhs.apply(Nat.Gt_0.of.Ne_0)

    Eq << Eq[-1].apply(Bool.Imp.given.All)

    n_ = Symbol('n', integer=True, positive=True)
    Eq << Algebra.All.given.Cond.subst.apply(Eq[-1], Eq[-1].variable, n_)

    Eq << Eq[-1].this.lhs.apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.lhs.find(Factorial).apply(Discrete.Factorial.eq.Mul)

    Eq << Eq[-1].this.find(Pow, Factorial).apply(Discrete.Factorial.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2020-09-29
from . import decrease
from . import increase
