from util import *


@apply
def apply(self):
    *sizes, d_x = self.shape
    assert not sizes
    [*args] = self.of(MatMul)
    for i, grad in enumerate(args):
        if grad.is_Derivative:
            fx, (x, S[1]) = grad.args
            break
    else :
        return

    assert i in (0, len(args) - 1)
    del args[i]
    assert not any(arg._has(x) for arg in args)
    args.append(fx)

    return Equal(self, Derivative[x](MatMul(*args)))


@prove
def prove(Eq):
    from Lemma import Calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    A = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(A @ Derivative[x](f(x)))


    Eq << Eq[0].this.rhs.apply(Calculus.Grad.Dot.eq.Dot.Grad)



if __name__ == '__main__':
    run()
# created on 2023-04-08
