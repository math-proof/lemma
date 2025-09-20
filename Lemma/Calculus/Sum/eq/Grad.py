from util import *


@apply
def apply(self, *, simplify=True):
    expr, *limits_d = self.of(Sum)
    f, *limits_s = expr.of(Derivative)

    f = Sum(f, *limits_d)
    if simplify:
        f = f.simplify()
    return Equal(self, Derivative(f, *limits_s))


@prove
def prove(Eq):
    from Lemma import Calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True)
    y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sum[x:n](Derivative[y](f(x, y))))

    Eq << Eq[0].this.rhs.apply(Calculus.Grad.eq.Sum)


if __name__ == '__main__':
    run()
# created on 2023-04-07
