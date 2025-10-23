from util import *


def rewrite(self, i=None, deep=False):
    args = self.of(MatMul)
    if i is None:
        for i, arg in enumerate(args):
            if arg.is_Add:
                break
        else:
            return self
    else :
        arg = args[i]
        if i < 0:
            i += len(args)

    if i > 0:
        former, latter = self.func(*args[:i]), args[i + 1:]
        if deep:
            func = lambda a : rewrite(former @ a, deep=True)
        else:
            func = lambda a : former @ a

        left = Add(*map(func, arg.of(Add)))
        if latter:
            left @= self.func(*latter)
        return left
    else:
        latter = self.func(*args[1:])
        if deep:
            func = lambda a : rewrite(a @ latter, deep=True)
        else:
            func = lambda a : a @ latter
        return Add(*map(func, arg.of(Add)))

@apply
def apply(self, i=None, deep=False):
    return Equal(self, rewrite(self, i, deep=deep), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Finset
    from sympy import Mul
    n = Symbol(integer=True, positive=True)
    x, a, b = Symbol(shape=(n, n), complex=True)
    Eq << apply(x @ (a + b))

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)


if __name__ == '__main__':
    run()

# created on 2020-11-10

# updated on 2023-06-24
del Mul
from . import shift
from . import of
from . import Mul
