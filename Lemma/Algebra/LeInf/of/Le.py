from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)
    assert Tuple.is_nonemptyset(limits)
    return LessEqual(Inf(lhs, *limits).simplify(), Inf(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(LessEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Logic.AllIn.of.All, (i, 0, n))

    Eq << Algebra.LeInf.of.All_Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-23
