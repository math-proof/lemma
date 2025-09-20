from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Equal[0]])
    shape = given.limits_shape

    return Equal(Stack(lhs, *limits), Zeros(*shape, *lhs.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:n](Equal(f(i), 0)))

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[1], j)

    Eq << Algebra.Cond.of.All.subst.apply(Eq[0], i, j)


if __name__ == '__main__':
    run()
# created on 2022-01-01
