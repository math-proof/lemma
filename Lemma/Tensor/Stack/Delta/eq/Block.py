from util import *


@apply
def apply(self):
    (c, hj), (j, S[0], n) = self.of(Stack[KroneckerDelta])
    if c._has(j):
        c, hj = hj, c

    b, a = hj.of_simple_poly(j)
    # a * j + b = c
    if a == 1:
        i = c - b
    elif a == -1:
        i = b - c

    if i == n - 1:
        rhs = BlockMatrix(Zeros(n - 1), 1)
    elif i == 0:
        rhs = BlockMatrix(1, Zeros(n - 1))
    else:
        assert n - i
        rhs = BlockMatrix(Zeros(i), 1, Zeros(n - i - 1))

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Int

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Stack[j:n](KroneckerDelta(n - 1, j)))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.apply(Int.Ite.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2021-12-30
# updated on 2022-01-04
