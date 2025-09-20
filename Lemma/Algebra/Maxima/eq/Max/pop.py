from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.pop import rewrite
    return Equal(self, rewrite(Maxima, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    Eq << apply(Maxima[i:n + 1](f(i)))


    Eq << Eq[-1].this.lhs.apply(Algebra.Maxima.eq.Max.split, cond={n})


if __name__ == '__main__':
    run()
# created on 2023-04-23
