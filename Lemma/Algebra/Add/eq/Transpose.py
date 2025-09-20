from util import *


@apply
def apply(self, evaluate=False):
    args = self.of(Add)
    rhs = Transpose(Add(*(arg.of(Transpose) for arg in args)).simplify(), evaluate=evaluate)
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, m = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(m, n))
    Eq << apply(A.T + B.T)
    i, j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2018-08-10
