from util import *


@apply
def apply(eq, f_eq, *, reverse=False, simplify=True, assumptions={}, index=None):
    from Lemma.Algebra.All.of.All_Eq.Cond.subst import subs
    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
    return eq, subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions, index=index)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real[m][n])
    Eq << apply(Equal(a, 2 * c), Element(a * b, S))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.lhs.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-08-26
