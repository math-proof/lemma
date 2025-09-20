from util import *


@apply
def apply(self):
    fx, *limits = self.of(ReducedArgMin[Stack])
    if fx.shape:
        return Equal(self, Stack(ReducedArgMin(fx), *limits))

    limit, *limits = limits
    return Equal(self, Stack(ReducedArgMin(Stack(fx, limit)), *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m,))
    i = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(ReducedArgMin(Stack[i:n](f(x))))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-17
