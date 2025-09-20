from util import *


@apply
def apply(contains1, contains2, w=None):
    x0, s = contains1.of(Element)
    x1, S[s] = contains2.of(Element)
    assert s.is_Interval

    assert 0 <= w <= 1
    return Element(x0 * w + x1 * (1 - w), s)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, b, x0, x1 = Symbol(real=True)
    domain = Interval(a, b, left_open=True)
    w = Symbol(domain=Interval(0, 1))
    Eq << apply(Element(x0, domain), Element(x1, domain), w)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=w > 0)

    Eq << (w <= 0).this.apply(Algebra.Eq.of.Le.squeeze.Icc)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.of.Cond.apply(Eq[1], cond=w<=0)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[3], cond=w < 1)

    Eq.open_Interval, Eq.ge = Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << (w >= 1).this.apply(Algebra.Eq.of.Ge.squeeze)

    Eq <<= Eq[-1] & Eq.ge

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=w >= 1)

    Eq << Eq.open_Interval.this.lhs.apply(Set.In.Icc.of.Lt.Gt, simplify=None)

    Eq << Logic.Imp.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.In.Icc.Ioo.of.In.In.In)





if __name__ == '__main__':
    run()

# created on 2020-05-08
# updated on 2023-08-26
from . import In
