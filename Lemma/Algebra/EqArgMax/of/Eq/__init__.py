from util import *



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(ArgMax(lhs, *limits).simplify(), ArgMax(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), real=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Bool.EqUFnS.of.Eq.apply(Eq[0], ArgMax[i:n], simplify=False)

if __name__ == '__main__':
    run()

# created on 2019-04-04
from . import definition
