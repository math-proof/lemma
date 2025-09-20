from util import *


@apply
def apply(all_le):
    (fx, M), *limits = all_le.of(All[LessEqual])
    assert not M.has(*(v for v, *_ in limits))
    return Sup(fx, *limits) <= M


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(All[x:S](f(x) <= M))

    Eq << Eq[1].this.lhs.apply(Algebra.Sup.eq.ReducedMin)

    m = Symbol(Eq[-1].lhs)
    Eq << m.this.definition

    Eq << Algebra.All.Le.of.Eq_ReducedMin.apply(Eq[-1])

    y = Eq[-1].variable
    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Eq[-1].subs(y, M)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.definition




if __name__ == '__main__':
    run()
# created on 2019-01-17
# updated on 2023-04-14
