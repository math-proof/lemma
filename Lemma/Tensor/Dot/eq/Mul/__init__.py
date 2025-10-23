from util import *


@apply(simplify=False)
def apply(self, i=None, factor=None):
    [*args] = self.of(MatMul)
    if i is None:
        for i, arg in enumerate(args):
            if arg.is_Add:
                break
        else:
            return
    else :
        arg = args[i]
        assert arg.is_Add

    if factor is None:
        from Lemma.Nat.AddMulS.eq.Mul_Add import rewrite
        arg, factor = rewrite(arg)
    else:
        factor = sympify(factor)
        arg = Add(*(arg * factor for arg in arg.args))
        factor = 1 / factor
    assert not factor.shape
    args[i] = arg

    return Equal(self, factor * MatMul(*args), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    a = Symbol(real=True)
    Eq << apply(A @ (a * B - a * C) @ D)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2023-04-30


# updated on 2023-05-01
from . import adjugate
