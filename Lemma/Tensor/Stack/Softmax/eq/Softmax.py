from util import *


@apply
def apply(self):
    x, *limits = self.of(Stack[Softmax])

    return Equal(self, Softmax(Stack(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    i = Symbol(integer=True)
    Eq << apply(Stack[i:m](Softmax(x[i])))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)






if __name__ == '__main__':
    run()
# created on 2022-01-11
