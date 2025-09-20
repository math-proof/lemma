from util import *


@apply
def apply(self):
    (x, *limits), e = self.of(Stack ** Expr)
    return Equal(self, Stack(x ** e, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    e = Symbol(real=True)
    Eq << apply(Stack[i:n](x[i]) ** e)

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2021-12-21
