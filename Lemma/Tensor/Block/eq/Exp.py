from util import *



def extract(cls, self):
    if self.is_BlockMatrix:
        axis = self.axis
        args = self.args
        args = [extract(cls, arg) for arg in args]
        return BlockMatrix[axis](*args, shape=self.shape)
    return self.of(cls)

@apply
def apply(self):
    return Equal(self, Exp(extract(Exp, self)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(positive=True, integer=True)
    A, B, C, D = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix([[exp(A), exp(B)], [exp(C), exp(D)]]))

    Eq << Eq[-1].this.rhs.apply(Algebra.Exp.eq.Block)




if __name__ == '__main__':
    run()
# created on 2023-06-08
