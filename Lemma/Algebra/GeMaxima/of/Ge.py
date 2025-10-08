from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(GreaterEqual)
    assert Tuple.is_nonemptyset(limits)
    return GreaterEqual(Maxima(lhs, *limits).simplify(), Maxima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Bool.AllIn.of.All, (i, 0, n))

    Eq << Algebra.GeMaximaS.of.All_Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-23
