from util import *


@apply
def apply(self):
    x, *limits = self.of(Sign[Stack])
    return Equal(self, Stack(Sign(x), *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Sign(Stack[i:n](x[i])))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2023-05-24
