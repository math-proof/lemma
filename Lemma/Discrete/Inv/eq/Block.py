from util import *


@apply
def apply(self):
    blocks = self.of(MatPow[Expr, -1]).blocks
    index = -1
    is_lower = None
    for i in range(len(blocks)):
        blocks[i] = [*blocks[i]]
        for j in range(len(blocks[i])):
            if j == i:
                assert blocks[i][j].is_Identity or blocks[i][j].is_One
            elif blocks[i][j].is_zero:
                ...
            elif index >= 0:
                assert j == index
            else:
                index = j
                blocks[i][j] = -blocks[i][j]
                if is_lower is None:
                    is_lower = i < j
                else:
                    assert is_lower == i < j

    return Equal(self, BlockMatrix(blocks))

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    n, k, l = Symbol(integer=True, positive=True)
    # X = Symbol(real=True, shape=(n - k - l, l))
    X = Symbol(real=True, shape=(k, l))
    Eq << apply(
        BlockMatrix([
            [Identity(k), X, Zeros(k, n - k - l)],
            [Zeros(l, k), Identity(l), Zeros(l, n - k - l)],
            [Zeros(n - k - l, k), Zeros(n - k - l, l), Identity(n - k - l)]
        ]) ^ -1)

    Eq << (Eq[0].lhs.find(BlockMatrix) @ Eq[0].rhs).this.apply(Tensor.Dot.eq.Block, True)

    Eq << Eq[-1].this.rhs.apply(Algebra.Block.eq.Eye)

    Eq << Tensor.EqInv.of.Eq_Dot.apply(Eq[-1], left=True)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2023-07-11
# updated on 2023-08-19
