from util import *


@apply
def apply(self, *, simplify=True):
    x, *limits = self.of(Stack[Exp])

    x_exp = Stack(exp(x), *limits)
    x = Stack(x, *limits)

    if simplify:
        x_exp = x_exp.simplify()
        x = x.simplify()

    return Equal(self, Softmax(x) * ReducedSum(x_exp))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    i = Symbol(integer=True)
    Eq << apply(Stack[i:m](exp(x[i])))

    Eq << Eq[0].this.lhs.apply(Tensor.Stack.eq.Exp)

    Eq << Eq[-1].this.lhs.apply(Tensor.Exp.eq.MulSoftmax_SumExp)



if __name__ == '__main__':
    run()
# created on 2022-01-10
