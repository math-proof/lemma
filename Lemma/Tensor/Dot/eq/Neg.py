from util import *


@apply(simplify=False)
def apply(self, i=None):
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

    args[i] = Add(*[-arg for arg in arg.args])

    return Equal(self, -MatMul(*args), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    Eq << apply(A @ (B - C) @ D)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add)




if __name__ == '__main__':
    run()
# created on 2023-04-30
