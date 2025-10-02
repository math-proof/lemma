from util import *


@apply
def apply(self):
    prod = self.of(Log)

    rhs = Sum(self.func(prod.function), *prod.limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    j, i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply(Log(Product[i:n, j:n](f(j, i))))

    Eq << Algebra.Eq.given.EqExpS.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-12-11
