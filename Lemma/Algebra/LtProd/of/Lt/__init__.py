from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)
    assert lhs.is_positive

    return Less(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), real=True, positive=True)

    Eq << apply(Less(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Bool.AllIn.of.All, (i, 0, n))

    Eq << Algebra.LtProd.of.All_Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-01-01
del Lt
from . import Lt
