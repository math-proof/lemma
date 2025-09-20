from util import *


@apply
def apply(self):
    f, *limits_d = self.of(Derivative[ReducedSum])
    if len(limits_d) > 1:
        return
    
    (x, S[1]), = limits_d
    if x.shape:
        if len(x.shape) == 1:
            return Equal(self, ReducedSum(Derivative[x](f).doit().T))
    else:
        return Equal(self, ReducedSum(Derivative[x](f).doit()))


@prove(proved=False)
def prove(Eq):
    n, d = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(d,))
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[x](ReducedSum(f(x))))

    


if __name__ == '__main__':
    run()
# created on 2023-03-17
