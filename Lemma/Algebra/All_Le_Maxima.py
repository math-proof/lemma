from util import *


@apply
def apply(self):
    function, *limits = self.of(Maxima)
    return All(LessEqual(function, self), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Maxima[x:S](f(x)))


    Eq << Algebra.All_GeMaxima.apply(Eq[0].find(Maxima))

    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2023-03-28
