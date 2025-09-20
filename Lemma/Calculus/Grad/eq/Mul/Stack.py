from util import *


@apply
def apply(self, i=None):
    expr, *limits_d = self.of(Derivative)
    (x, S[1]), = limits_d
    if i is None:
        i = Symbol(integer=True)
    expr = expr._subs(x, x[i])
    n, = x.shape
    return Equal(self, Identity(n) * Stack[i:n](Derivative[x[i]](expr)))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Tensor

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[x](f(x)))

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], j)

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.eq.Mul.Grad)












if __name__ == '__main__':
    run()
# created on 2023-03-18
