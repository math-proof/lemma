from util import *


@apply
def apply(self, i=None):
    expr, *limits_d = self.of(Derivative @ Ones)
    (x, S[1]), = limits_d
    if i is None:
        i = self.generate_var(integer=True)
    expr = expr._subs(x, x[i])
    n, = self.shape

    return Equal(self, Stack[i:n](Derivative[x[i]](expr)))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[x](f(x)) @ Ones(n))

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Mul.Stack)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)

    Eq << Eq[-1].this.find(Mul).apply(Tensor.Mul.Stack.eq.Stack)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Sum)




if __name__ == '__main__':
    run()
# created on 2023-03-19
