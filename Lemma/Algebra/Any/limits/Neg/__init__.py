from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from Lemma.Algebra.All.of.All.limits.Neg import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.Neg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Any.limits.Neg)


if __name__ == '__main__':
    run()

# created on 2019-02-19
from . import Infty
