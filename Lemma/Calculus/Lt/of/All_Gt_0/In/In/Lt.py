from util import *


@apply
def apply(all_is_positive, contains0, contains1, le):
    (fx, (x, S[1])), (S[x], a, b) = all_is_positive.of(All[Derivative > 0])
    x0, domain = contains0.of(Element)
    assert domain.left_open and domain.right_open
    S[a], S[b] = domain.of(Interval)

    x1, S[domain] = contains1.of(Element)

    S[x0], S[x1] = le.of(Less)

    f = lambda t: fx._subs(x, t)
    return f(x0) < f(x1)


@prove(proved=False)
def prove(Eq):
    from Lemma import Set

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0), Element(x0, domain), Element(x1, domain), x0 < x1)

    Eq << Eq[0].this.expr.apply(Set.IsExtendedReal.of.Gt, simplify=None)

    Eq.subset = Set.Subset.Icc.of.In.In.apply(Eq[1], Eq[2])

    Eq << Set.All.of.Subset.All.apply(Eq.subset, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-04-01
