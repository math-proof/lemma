from util import *


@apply
def apply(self):
    assert not self.shape
    x, *args = self.of(ReducedArgMax[BlockMatrix])
    n, = x.shape
    y = BlockMatrix(*args)

    i = self.generate_var(domain=Range(n))
    if x[i] < y[0]:
        ...
    else:
        if x[i] <= y[0]:
            print("this proof is not safe!")
        else:
            if x.is_extended_negative and x.is_infinite:
                print("this proof is not safe though x is negative infinite")
            else:
                raise
    return Equal(self, n + ReducedArgMax(y))


@prove(proved=False)
def prove(Eq):
    b, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,), positive=True)
    Eq << apply(ReducedArgMax(BlockMatrix(Zeros(b), x, Zeros(b))))

    


if __name__ == '__main__':
    run()
# created on 2021-12-20
# updated on 2022-01-03