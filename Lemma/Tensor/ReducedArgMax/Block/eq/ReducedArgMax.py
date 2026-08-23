from util import *


@apply
def apply(self):
    assert not self.shape
    x, *args = self.of(ReducedArgMax[BlockMatrix])
    y = BlockMatrix(*args)
    n, = x.shape
    i = self.generate_var(integer=True, var='i', domain=Range(y.shape[0]))
    if x[n - 1] >= y[i]:
        ...
    else:
        if y.is_extended_negative and y.is_infinite:
            print("this proof is not safe though y is negative infinite")
        else:
            raise
    return Equal(self, ReducedArgMax(x))


@prove(proved=False)
def prove(Eq):
    b, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,), nonnegative=True)
    Eq << apply(ReducedArgMax(BlockMatrix(x, Zeros(b))))





if __name__ == '__main__':
    run()
# created on 2021-12-20
