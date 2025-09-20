from util import *


@apply
def apply(self):
    i_shape, *shape = self.shape
    assert shape
    assert isinstance(i_shape, int) or i_shape.is_Number
    array = []
    for i in range(i_shape):
        array.append(self[sympify(i)])
    rhs = BlockMatrix(*array, shape=self.shape)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(oo, n))
    Eq << apply(a[i:i + 4])

    Eq << Equal(a[i:i + 4], Stack[j:4](a[i + j]), plausible=True)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Block)


if __name__ == '__main__':
    run()
# created on 2020-03-12
