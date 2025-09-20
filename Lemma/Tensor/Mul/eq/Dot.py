from util import *


@apply
def apply(self, index=None):
    args = [*self.args]
    for i, matrix in enumerate(args):
        if matrix.is_MatMul:
            break
    else:
        return

    args[i] = 1

    factor = Mul(*args)
    assert not factor.shape
    [*args] = matrix.args

    if index is None:
        for index, arg in enumerate(args):
            func = arg.func
            if func.is_Add or func.is_Stack:
                break
        else:
            return
    else:
        arg = args[index]
        func = arg.func

    arg *= factor
    if func.is_Add:
        arg = arg.expand()
    elif func.is_Stack:
        from Lemma.Tensor.Mul.eq.Stack import rewrite
        arg = rewrite(arg)

    args[index] = arg

    return Equal(self, MatMul(*args, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    m, n, d = Symbol(integer=True, positive=True)
    A, C = Symbol(real=True, shape=(m, n))
    B = Symbol(real=True, shape=(n, d))
    x = Symbol(real=True)
    Eq << apply((A + C) @ B * x)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.lhs.find(MatMul).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2023-04-07
