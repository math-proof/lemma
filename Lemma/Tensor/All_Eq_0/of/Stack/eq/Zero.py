from util import *


@apply
def apply(given):
    lhs, *limits = given.of(Equal[Stack, Zeros])

    return All(Equal(lhs, Zeros(*lhs.shape)), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Equal(Stack[i:n](f(i)), Zeros(n)))

    j = Symbol(domain=Range(n))
    Eq << Eq[0][j]

    Eq << Algebra.All.of.Cond.domain_defined.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-01
