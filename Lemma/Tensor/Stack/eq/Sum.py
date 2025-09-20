from util import *


@apply
def apply(self):
    (function, *sgm_limits), *limits = self.of(Stack[Sum])
    rhs = Sum(Stack(function, *limits).simplify(), *sgm_limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, n), real=True)
    Eq << apply(Stack[i:n](Sum[j:n](x[j, i])))
    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2019-10-21
