from util import *


@apply
def apply(self, pivot):
    assert self.is_Ones
    n, *shape = self.shape
    assert pivot < n and pivot > 0
    return Equal(self, BlockMatrix([Ones(pivot, *shape), Ones(n - pivot, *shape)]), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m = 4
    n = 5
    Eq << apply(Ones(4, 5), pivot=2)

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)







if __name__ == '__main__':
    run()
# created on 2021-10-07
# updated on 2021-10-09
