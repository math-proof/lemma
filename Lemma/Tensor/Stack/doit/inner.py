from util import *


def doit(self):
    xi, (i, a, b), *limits = self.of(Stack[Tuple])
    assert i.is_integer

    diff = b - a
    assert diff == int(diff)

    arr = [xi._subs(i, a + t) for t in range(diff)]

    assert limits, "try to invoke Tensor.Stack.eq.Matrix"
    return Stack(BlockMatrix(arr), *limits)


@apply
def apply(self):
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = 5
    Eq << apply(Stack[j:n, i:m](x[i, j]))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.Matrix)




if __name__ == '__main__':
    run()
# created on 2022-07-08
