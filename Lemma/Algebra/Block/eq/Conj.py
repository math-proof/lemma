from util import *


def extract(self):
    if self.is_BlockMatrix:
        axis = self.axis
        args = self.args
        args = [extract(arg) for arg in args]
        return BlockMatrix[axis](*args, shape=self.shape).simplify()
    return ~self

@apply
def apply(self):

    return Equal(self, Conjugate(extract(self), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(positive=True, integer=True)
    A, B, C, D = Symbol(shape=(n, n), complex=True)
    Eq << apply(BlockMatrix([[~A, ~B], [~C, ~D]]))

    Eq << Eq[-1].this.rhs.apply(Algebra.Conj.eq.Block)




if __name__ == '__main__':
    run()
# created on 2023-09-18
