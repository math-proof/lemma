from util import *


@apply
def apply(given):
    return given.domain_definition() >> given


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True)
    f = Function(complex=True, shape=())
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(1 / f(x) > 0)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Eq[1].lhs)

    Eq << Eq[0].cond.invert().this.apply(Algebra.Ne_0.of.Div1.gt.Zero)

    Eq << Eq[-1].this.apply(Bool.Imp.Is.ImpNotS)




if __name__ == '__main__':
    run()
# created on 2023-10-13
