from util import *


@apply
def apply(self):
    from Lemma.Random.Sum.eq.Expect import rewrite
    return Equal(self, rewrite(Integral, self))


@prove
def prove(Eq):
    from Lemma import Random

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    x, s = Symbol(real=True, random=True)
    Eq << apply(Integral[x.bvar](Pr[x:θ](x | s) * f(x.bvar)))

    Eq << Eq[-1].this.rhs.apply(Random.Expect.eq.Integral_Mul_Prob)




if __name__ == '__main__':
    run()
# created on 2023-04-02
