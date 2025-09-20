from util import *


@apply
def apply(self):
    assert self.is_Ones
    indices, limits = self.variables_with_limits()

    return Equal(self, Stack(S.One, *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m, n = Symbol(integer=True, positive=True)
    Eq << apply(Ones(m, n))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
# created on 2023-03-19
