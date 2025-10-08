from util import *


@apply
def apply(is_real, given, epsilon=None, delta=None):

    l, a = given.of(Equal)
    if a.is_Limit:
        l, a = a, l

    S[a], S[Reals] = is_real.of(Element)

    _a = l.generate_var(excludes=l.variable, real=True)
    given = given._subs(a, _a)
    from Lemma.Calculus.Eq.Is.Any_All.limit_definition import Any_All
    given = Any_All(given, epsilon, delta)
    return given._subs(_a, a)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Calculus, Bool

    n = Symbol(integer=True, positive=True)
    x, x0 = Symbol(real=True)
    f = Function(real=True, shape=())
    a = Symbol(complex=True)
    Eq << apply(Element(a, Reals), Equal(Limit[x:x0 + S.Infinitesimal](f(x)), a))

    Eq << Set.Any.Eq.of.In.apply(Eq[0], var='A')

    Eq << Bool.Any_And.of.Any.All.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.expr.args[1].apply(Calculus.Any.All.of.Eq_Limit.limit_definition)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-23
