from util import *


@apply
def apply(self):
    (expr, (x, a, b)), (S[expr], (S[x], S[a], _b)) = self.of(Integral - Integral)

    return Equal(self, Integral[x:_b:b](expr))


@prove
def prove(Eq):
    from Lemma import Calculus

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) - Integral[x:a:c](f(x)))

    Eq << Eq[0] + Eq[0].find(Mul[~Integral])

    Eq << Eq[-1].this.rhs.apply(Calculus.Add.eq.Integral.concat)



if __name__ == '__main__':
    run()
# created on 2020-04-30
# updated on 2023-03-21
