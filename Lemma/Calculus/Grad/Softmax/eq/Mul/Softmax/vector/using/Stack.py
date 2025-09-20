from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[softmax])
    n, = x.shape
    dfx = Derivative[x](fx).doit()
    return Equal(self, ((dfx.T - ((dfx @ Ones(n)) * Softmax(fx))) * Softmax(fx)).T)


@prove
def prove(Eq):
    from Lemma import Tensor, Calculus, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](softmax(f(x))))

    i = Symbol(integer=True)
    Eq << Derivative[x[i]](log(softmax(f(x)))).this.find(softmax).apply(Tensor.Softmax.eq.Mul.ReducedSum)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(Derivative[ReducedSum]).apply(Calculus.Grad.eq.ReducedSum)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Sum[Mul[~Derivative]]).apply(Calculus.Grad.eq.Mul.Grad)

    Eq << Eq[-1].this(i).find(Element).simplify()

    # using lamda
    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1] * Eq[-1].find(Softmax)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Exp).apply(Tensor.Exp.eq.Mul.Softmax)

    Eq << Eq[-1].this.find(Stack).apply(Calculus.Stack.Grad.eq.Dot)

    Eq << Eq[-1].T





if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-03-19
