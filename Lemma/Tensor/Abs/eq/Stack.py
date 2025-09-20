from util import *


@apply
def apply(self):
    x, *limits = self.of(Abs[Stack])
    return Equal(self, Stack(Abs(x), *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(abs(Stack[i:n](x[i])))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-21
