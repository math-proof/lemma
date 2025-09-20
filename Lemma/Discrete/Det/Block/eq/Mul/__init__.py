from util import *



def find_zero_matrix(row, n):
    for i, cell in enumerate(row):
        if cell.is_Zeros:
            if len(cell.shape) == 2:
                a, b = cell.shape
                if a + b == n:
                    return i
            elif len(cell.shape) == 1:
                a, = cell.shape
                if a + 1 == n:
                    return i


def swap_row(blocks, i, j):
    blocks[i], blocks[j] = blocks[j], blocks[i]

    if i < j:
        start = i + 1
        stop = j
    elif i > j:
        start = j + 1
        stop = i
    else:
        return 0

    x = blocks[i][0].shape[-2]
    y = blocks[j][0].shape[-2]

    return x * y + sum([blocks[k][0].shape[-2] for k in range(start, stop)]) * (x + y)


@apply
def apply(self):
    from Lemma.Discrete.DetBlock.eq.PowNegativeOneMul import swap_col
    X = self.of(Det)
    blocks = [[*b] for b in X.blocks]
    n = X.shape[0]
    for i, row in enumerate(blocks):
        j = find_zero_matrix(row, n)
        if j is not None:
            break
    else:
        return

    if i:
        s = swap_row(blocks, 0, i)
        i = 0
    else:
        s = 0

    if j != len(blocks[0]) - 1:
        s += swap_col(blocks, j, len(blocks[0]) - 1)
        j = -1

    B = [None] * len(blocks)
    for t, row in enumerate(blocks):
        B[t] = row[j]

    del B[i]
    if len(B) == 1:
        B, = B
    else:
        B = BlockMatrix(B)

    if B.shape:
        B = det(B)

    A = blocks[i]
    del A[j]

    if len(A) == 1:
        A, = A
    else:
        A = BlockMatrix[1](A)

    if A.shape:
        A = det(A)

    return Equal(self, (-1) ** s * A * B)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    B = Symbol(shape=(n, 2 * n), complex=True)
    C = Symbol(shape=(n, n), complex=True)
    D = Symbol(shape=(2 * n, n), complex=True)
    E = Symbol(shape=(2 * n, n), complex=True)
    F = Symbol(shape=(n, n), complex=True)
    G = Symbol(shape=(n, 2 * n), complex=True)
    H = Symbol(shape=(n, n), complex=True)
    Eq << apply(Determinant(BlockMatrix([[A, B, C], [D, Zeros(2 * n, 2 * n), E], [F, G, H]])))

    Eq << (BlockMatrix([[Zeros(2 * n, n), Identity(2 * n), Zeros(2 * n, n)], [Identity(n), Zeros(n, 2 * n), Zeros(n, n)], [Zeros(n, n), Zeros(n, 2 * n), Identity(n)]]) @ Eq[0].lhs.arg).this.apply(Tensor.Dot.eq.Block, True)

    Eq << Eq[-1] @ BlockMatrix([[Identity(n), Zeros(n, n), Zeros(n, 2 * n)], [Zeros(2 * n, n), Zeros(2 * n, n), Identity(2 * n)], [Zeros(n, n), Identity(n), Zeros(n, 2 * n)]])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, True)

    X = Symbol(BlockMatrix([D.T, E.T]).T)
    Y = Symbol(BlockMatrix([B, G]))
    Z = Symbol(BlockMatrix([[A, C], [F, H]]))
    Eq << BlockMatrix([[X, Zeros(2 * n, 2 * n)], [Z, Y]]).this.find(Symbol).definition

    Eq << Eq[-1].this.rhs.args[1].find(Symbol).definition

    Eq << Eq[-1].this.rhs.args[1].args[-1].definition

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Discrete.Det.Block.eq.Mul.deux)

    Eq << Eq[-1].this.rhs.find(Symbol).definition

    Eq << Eq[-1].this.rhs.find(Symbol).definition

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1].this.lhs.args[-1].apply(Discrete.DetBlock.eq.PowNegativeOneMul)

    Eq << Eq[-1].this.lhs.args[-1].apply(Discrete.DetBlock.eq.PowNegativeOneMul)





if __name__ == '__main__':
    run()

# created on 2021-11-21
# updated on 2022-01-15
from . import Prod
from . import deux
