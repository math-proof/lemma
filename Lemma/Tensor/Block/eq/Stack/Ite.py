from util import *


@apply
def apply(self, var=None):
    assert self.is_BlockMatrix
    axis = self.axis

    indices = []
    limits = []
    for i in range(axis + 1):
        j = self.generate_var({*indices}, integer=True, var=var)

        indices.append(j)
        limits.append((j, 0, self.shape[i]))

    limits.reverse()
    rhs = Stack(self[indices], *limits)

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n0, n1, n2, n3, m = Symbol(positive=True, integer=True)
    A = Symbol(shape=(m, n0), real=True)
    B = Symbol(shape=(m, n1), real=True)
    C = Symbol(shape=(m, n2), real=True)
    D = Symbol(shape=(m, n3), real=True)
    Eq << apply(BlockMatrix[1](A, B, C, D))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n0 + n1 + n2 + n3))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)





if __name__ == '__main__':
    run()
# created on 2021-12-20
# updated on 2023-04-29
