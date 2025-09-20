from util import *


@apply
def apply(self, index=-1):
    print('use BlockMatrix.subs instead, which is more flexible')
    args = self.of(BlockMatrix)
    if index < 0:
        index += len(args)

    zeroMatrix = args[index]
    assert not zeroMatrix
    n, = zeroMatrix.shape
    assert args[index - 1] == 0
    args = args[:index - 1] + (Zeros(n + 1),) + args[index + 1:]

    return Equal(self, BlockMatrix(args))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True)
    Eq << apply(BlockMatrix([x, 0, Zeros(n)]))

    i = Symbol(domain=Range(n + 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-11-21
# updated on 2021-11-22
