from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    return self <= Sum(Abs(expr), *limits)


@prove
def prove(Eq):
    from Lemma import Int, Finset

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:n](f(k)))

    Eq << Int.GeAbs.apply(f(k))

    Eq << Finset.LeSum.of.Le.apply(Eq[-1], (k, 0, n))


if __name__ == '__main__':
    run()
# created on 2023-04-15
