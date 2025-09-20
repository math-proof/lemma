from util import *


@apply
def apply(self, pivot=-1, *, simplify=True):
    assert self.is_BlockMatrix
    if not isinstance(pivot, (list, tuple)):
        pivot = [pivot] * len(self.args)
    former, latter = zip(*([Mul(*s) for s in std.array_split(expr.of(Mul), pivot)] for expr, pivot in zip(self.args, pivot)))
    axis = self.axis
    former, latter = BlockMatrix[axis](*former), BlockMatrix[axis](*latter)
    if simplify:
        former, latter = former.simplify(), latter.simplify()
    return Equal(self, Mul(former, latter, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(BlockMatrix(A * C, B * D))

    Eq << Eq[0].this.rhs.apply(Algebra.Mul.Block.eq.Block)




if __name__ == '__main__':
    run()
# created on 2023-06-08
