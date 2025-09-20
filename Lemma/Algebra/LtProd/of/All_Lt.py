from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Less])
    assert lhs.is_positive

    return Less(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True, positive=True)

    Eq << apply(All[i:n](Less(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << Algebra.GtProd.of.All_Gt.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-01-29
