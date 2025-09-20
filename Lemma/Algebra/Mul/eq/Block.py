from util import *

def rewrite(self, deep=True):
    shape = self.shape
    for i, block in enumerate(self.args):
        if isinstance(block, BlockMatrix) and block.shape == shape:
            break
    else:
        return self

    args = [*self.args]
    del args[i]
    factor = Mul(*args)
    axis = block.axis
    if axis == 0 or not factor.shape:
        if deep:
            return BlockMatrix[axis]([rewrite(b * factor, deep=True) for b in block.args])
        return BlockMatrix[axis]([b * factor for b in block.args])

    if axis == 1:
        if factor.is_BlockMatrix:
            if len(factor.shape) == 1:
                args = []
                for b, f in zip(block.args, factor.args):
                    if b.shape[-len(f.shape):] != f.shape:
                        break
                    args.append(b * f)
                else:
                    return BlockMatrix[axis](args)

    return self

@apply
def apply(self, deep=True):
    return Equal(self, rewrite(self, deep=deep))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m, n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(m, n))
    x = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(BlockMatrix(A, B) * x[i])

    j = Symbol(domain=Range(m * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ite.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2021-12-30
