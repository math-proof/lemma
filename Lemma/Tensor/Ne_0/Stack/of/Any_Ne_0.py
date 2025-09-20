from util import *


@apply
def apply(given):
    lhs, *limits = given.of(Any[Unequal[0]])
    shape = given.limits_shape

    return Unequal(Stack(lhs, *limits), Zeros(*shape, *lhs.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:n](Unequal(f(i), 0)))

    Eq << ~Eq[1]

    Eq << Tensor.All_Eq_0.of.Stack.eq.Zero.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-01-01
