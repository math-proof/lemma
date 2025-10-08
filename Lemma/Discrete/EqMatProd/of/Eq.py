from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(MatProduct(lhs, *limits).simplify(), MatProduct(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Bool
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Bool.All.of.Cond.apply(Eq[0], i)

    Eq << Discrete.EqMatProd.of.All_Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-10-29
