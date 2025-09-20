from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    return self <= Sum(Abs(expr), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:n](f(k)))

    Eq << Algebra.Le_Abs.apply(f(k))

    Eq << Algebra.LeSum.of.Le.apply(Eq[-1], (k, 0, n))


if __name__ == '__main__':
    run()
# created on 2023-04-15
