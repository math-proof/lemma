from util import *


@apply
def apply(contains, contains0, contains1, all_is_positive, swap=False):
    (fx, (x, S[2])), (S[x], a, b) = all_is_positive.of(All[Derivative > 0])

    x0, domain = contains0.of(Element)
    S[a], S[b] = domain.of(Interval)

    w, interval = contains.of(Element)
    assert interval != domain
    assert interval in Interval(0, 1)

    x1, S[domain] = contains1.of(Element)
    if swap:
        x0, x1 = x1, x0

    return GreaterEqual(w * fx._subs(x, x0) + (1 - w) * fx._subs(x, x1), fx._subs(x, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    w, x, x0, x1, a, b = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(Element(w, Interval(0, 1, right_open=True)), Element(x0, domain), Element(x1, domain), All[x:domain](Derivative(f(x), (x, 2)) > 0))

    w_ = Symbol('w', domain=Eq[0].rhs)
    x_ = Symbol('x', domain=domain)
    Eq << Algebra.Cond.of.All.subst.apply(Eq[3], x, x_)

    Eq << Calculus.Ge.of.Gt_0.Jesson.apply(Eq[-1], w=w_)

    Eq << Logic.All.of.Cond.apply(Eq[-1], w_)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    x0 = Eq[-1].lhs.find(f).arg
    Eq << Logic.All.of.Cond.apply(Eq[-1], x0)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[1], Eq[-1])

    x1 = Eq[-1].lhs.find(Add * ~f).arg
    Eq << Logic.All.of.Cond.apply(Eq[-1], x1)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-12
