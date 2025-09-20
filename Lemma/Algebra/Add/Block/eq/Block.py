from util import *


@apply
def apply(self):
    size = None
    blocks = []
    axis = None
    for block in self.of(Add):
        assert block.is_BlockMatrix
        args = block.args
        if size is None:
            size = len(args)
        else:
            assert size == len(args)

        if axis is None:
            axis = block.axis
        else:
            assert axis == block.axis

        blocks.append(args)

    args = []
    for i in range(size):
        additives = [block[i] for block in blocks]
        assert len({a.shape for a in additives}) == 1
        args.append(Add(*additives))

    return Equal(self, BlockMatrix[axis](*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(Add(BlockMatrix(A, B), BlockMatrix(C, D)))

    i = Symbol(domain=Range(m * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Algebra.AddIteS.eq.IteAnd)






if __name__ == '__main__':
    run()
# created on 2018-08-04
# updated on 2021-12-30
