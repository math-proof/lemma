from util import *


@apply
def apply(self):
    (expr, (x, a, b)), (S[expr], (S[x], _b, c)) = self.of(Integral + Integral)
    if b != _b:
        a, b, _b, c = _b, c, a, b
        assert _b == b

    return Equal(self, Integral[x:a:c](expr))


@prove(provable=False)
def prove(Eq):
    from Lemma import Calculus

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) + Integral[x:b:c](f(x)))

    # Eq << Eq[0].this.find(Integral).apply(Calculus.Integral.to.limit.maxima.Darboux)

    


if __name__ == '__main__':
    run()
# created on 2023-03-21
