from util import *


@apply
def apply(self):
    assert self.is_Ones
    array = 1
    for n in self.shape[::-1]:
        n = int(n)
        array = (array,) * n
    return Equal(self, Matrix(array), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m = 4
    n = 5
    Eq << apply(Ones(4, 5))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)





if __name__ == '__main__':
    run()
# created on 2021-10-04
