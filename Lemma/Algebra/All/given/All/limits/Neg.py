from util import *


@apply
def apply(self):
    from Lemma.Algebra.All.of.All.limits.Neg import negate
    expr, (i, *ab) = self.of(All)
    return All(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Lemma import Algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i) >= 0))

    Eq << Algebra.All.of.All.limits.Neg.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-12-09
