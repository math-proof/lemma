from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from Lemma.Algebra.All.of.All.limits.Neg import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Lemma import Algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << Algebra.Any.of.Any.limits.Neg.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-02-14

from . import Infty
