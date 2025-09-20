from util import *


@apply
def apply(self):
    function, *limits = self.of(Inf)
    return All(GreaterEqual(function, self), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Inf[x:S](f(x)))

    Eq << Algebra.All_LeInf.apply(Eq[0].find(Inf))

    Eq << Eq[-1].this.expr.reversed




if __name__ == '__main__':
    run()
# created on 2023-03-28
