from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Logic

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(Logic.All.given.Imp)

    Eq << Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Eq[-1].this.lhs.apply(Set.Eq.of.Ge.In)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=a < b)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.All.Ge.of.Lt.All_Ge_0.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2023-10-03
