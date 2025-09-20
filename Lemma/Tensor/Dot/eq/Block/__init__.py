from util import *

def outer_prod(args_A, B, deep=False):
    args_B = B.blocks
    if args_B:
        args_B = [BlockMatrix(b) for b in zip(*args_B)]
    else:
        args_B = B.of(BlockMatrix[1])

    if args_B:
        rows = len(args_A)
        cols = len(args_B)
        blocks = [[None] * cols for _ in range(rows)]
        for i in range(rows):
            for j in range(cols):
                if deep:
                    blocks[i][j] = matmul(args_A[i], args_B[j], True)
                else:
                    blocks[i][j] = args_A[i] @ args_B[j]
        return BlockMatrix(blocks)

def inner_prod(A, B, deep=False):

    if B.is_BlockMatrix:
        if B.axis == 1:
            if A.is_BlockMatrix:
                if args_A := A.blocks:
                    args_A = [BlockMatrix[1](a) for a in args_A]
                elif len(A.shape) == 1:
                    args_A = [A]
                else:
                    return

                return outer_prod(args_A, B, deep)

        else:
            args_B = B.args
            AT = A.T
            if AT.is_BlockMatrix and AT.axis == 0:
                args_A = AT.args

                assert len(args_A) == len(args_B)

                if deep:
                    args = []
                    for a, b in zip(args_A, args_B):
                        if len(a.shape) == 1 and len(b.shape) == 1:
#                             a is a column vector, b is a row vector
                            if a.is_Zeros or b.is_Zeros or \
                            a.is_BlockMatrix and all(not zero for zero in a.args) or \
                            b.is_BlockMatrix and all(not zero for zero in b.args):
                                arg = Zeros(*b.shape + a.shape)

                            elif a.is_Ones or a.is_BlockMatrix and all(one.is_Ones or one.is_One for one in a.args):
                                if b.is_BlockMatrix:
                                    arg = BlockMatrix[1]([Ones(*a.shape + b.shape) * b for b in b.args]).T
                                else:
                                    arg = Ones(*b.shape + a.shape) * b

                            elif b.is_Ones or b.is_BlockMatrix and all(one.is_Ones or one.is_One for one in b.args):
                                if a.is_BlockMatrix:
                                    arg = BlockMatrix[1]([Ones(*b.shape + a.shape) * a for a in a.args])
                                else:
                                    arg = Ones(*b.shape + a.shape) * a

                            else:
                                return
                        else:
                            arg = matmul(b.T, a, True)

                        args.append(arg)

                    from functools import reduce
                    return reduce(lambda a, b: a + b, args).T
                else:
                    args = []
                    for a, b in zip(args_A, args_B):
                        if len(a.shape) == 1 and len(b.shape) == 1:
#                             a is a column vector, b is a row vector
                            if a.is_Ones:
                                arg = Ones(*a.shape + b.shape) * b
                            elif b.is_Ones:
                                arg = Ones(*a.shape + b.shape) * a
                            else:
                                return
                        else:
                            arg = a.T @ b

                        args.append(arg)

                    return Add(*args)

def matmul(A, B, deep=False):

    if A.is_BlockMatrix:
        if A.axis == 0:
            args_A = A.args
            if B.is_BlockMatrix and len(B.shape) >= 2:
                if B.is_BlockMatrix:
                    if len(A.shape) == 1:
                        if (prod := inner_prod(A, B, deep)) is not None:
                            return prod

                    if (m := outer_prod(args_A, B, deep)) is not None:
                        return m

                else:
                    if (prod := inner_prod(A, B, deep)) is not None:
                        return prod
            else:
                if not B.shape:
                    return BlockMatrix(*[arg * B for arg in args_A])

                if len(B.shape) == 1:
                    args_A = A.of(BlockMatrix)
                    if len(A.shape) == 2:
                        if deep:
                            return BlockMatrix(*(matmul(a, B, deep=True) for a in args_A))
                        return BlockMatrix(*(a @ B for a in args_A))

                    args_B = B.of(BlockMatrix)
                    if args_B and args_A:
                        assert len(args_A) == len(args_B)
                        return Add(*(a @ b for a, b in zip(args_A, args_B)))
                else:
                    shape_B = B.shape
                    dotSize = shape_B[-2]
                    for arg in args_A:
                        shape = arg.shape
                        if not shape or shape[-1] != dotSize:
                            break
                    else:
                        if deep:
                            BlockMatrix(*[matmul(arg, B, True) for arg in args_A])
                        return BlockMatrix(*[arg @ B for arg in args_A])

                    if B.is_Ones:
                        if deep:
                            args = []
                            for arg in args_A:
                                shape = arg.shape
                                if shape:
                                    size = shape[-1]
                                else:
                                    size = 1

                                args.append(Ones(size, *shape_B[1:]))

                            B = BlockMatrix(args)
                            return inner_prod(A, B, deep=True)

        elif A.axis == 1:
            if (prod := inner_prod(A, B, deep)) is not None:
                return prod

    elif B.shape and A.shape:
        args_B = B.T.of(BlockMatrix)
        if args_B:
            return BlockMatrix(*[arg @ A.T for arg in args_B]).T

#         if deep:
#             if B.is_Add:
#                 return Add(*[A @ b for b in B.args])
    else:
        return A * B

    return A @ B


@apply
def apply(self, deep=False):
    A, B = self.of(MatMul)
    rhs = matmul(A, B, deep=deep)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    a, b, c, d, n, m = Symbol(integer=True, positive=True)
    A = Symbol(shape=(c, n), complex=True)
    B = Symbol(shape=(c, m), complex=True)
    C = Symbol(shape=(d, n), complex=True)
    D = Symbol(shape=(d, m), complex=True)
    _A = Symbol("A'", shape=(n, a), complex=True)
    _B = Symbol("B'", shape=(m, a), complex=True)
    _C = Symbol("C'", shape=(n, b), complex=True)
    _D = Symbol("D'", shape=(m, b), complex=True)
    Eq << apply(BlockMatrix([[A, B], [C, D]]) @ BlockMatrix([[_A, _C], [_B, _D]]), True)

    Eq << Eq[-1].lhs.this.apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul[BlockMatrix]).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul[BlockMatrix]).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(MatMul[BlockMatrix]).apply(Tensor.Dot.eq.Block.basic)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.Block.eq.Block)

    Eq << Eq[-1].this.rhs.find(Add[BlockMatrix]).apply(Algebra.Add.Block.eq.Block)





if __name__ == '__main__':
    run()

# created on 2020-08-18
# updated on 2021-12-13
from . import basic
