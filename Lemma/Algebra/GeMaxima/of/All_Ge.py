from util import *


@apply
def apply(given):
    (fx, m), *limits = given.of(All[GreaterEqual])
    assert Tuple.is_nonemptyset(limits)

    return GreaterEqual(Maxima(fx, *limits), m)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real, given=True, empty=False)
    f = Function(shape=(), complex=True)
    m = Symbol(real=True)
    Eq << apply(All[x:S](f(x) >= m))

    Eq << Algebra.All_GeMaxima.apply(Eq[1].lhs)

    Eq << Logic.All_And.of.All.All.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.of.Ge.Ge)




if __name__ == '__main__':
    run()
# created on 2023-03-25
