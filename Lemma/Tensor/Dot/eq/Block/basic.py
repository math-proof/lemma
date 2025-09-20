from util import *





@apply
def apply(self):
    from functools import reduce
    A, B = self.of(MatMul)
    if A.is_BlockMatrix:
        if A.axis == 0:
            args = A.args
            rhs = BlockMatrix([arg @ B for arg in args])
        elif A.axis == 1:
            if B.is_BlockMatrix:
                if B.axis == 0:
                    args_B = B.args
                    args_A = A.T.of(BlockMatrix)
                    assert len(args_A) == len(args_B)
                    args = [b.T @ a for a, b in zip(args_A, args_B)]
                    rhs = reduce(lambda a, b : a + b, args).T
                elif B.axis == 1:
                    args = B.T.of(BlockMatrix)
                    rhs = BlockMatrix([arg @ A.T for arg in args]).T
    elif B.is_BlockMatrix:
        if B.axis == 1:
            args = B.T.of(BlockMatrix)
            rhs = BlockMatrix([arg @ A.T for arg in args]).T

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    a, b, n, m = Symbol(integer=True, positive=True)
    C = Symbol(shape=(m, n), complex=True)
    A = Symbol(shape=(a, m), complex=True)
    B = Symbol(shape=(b, m), complex=True)
    Eq << apply(BlockMatrix(A, B) @ C)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    i = Symbol(domain=Range(a + b))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)




if __name__ == '__main__':
    run()
# created on 2021-11-20
# updated on 2023-06-08
