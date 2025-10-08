from util import *


@apply(simplify=False)
def apply(le, el):
    a, b = le.of(Greater)
    t, s = el.of(Element)
    assert s in Interval(-oo, oo)
    return Greater(a + t, b + t)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    x, y, a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(x > y, Element(t, Interval(a, b)))

    Eq << Set.In_Union.of.In.apply(Eq[1], Reals, simplify=None)

    z = Symbol(real=True)
    Eq << Set.Any.Eq.of.In.apply(Eq[-1], var=z)

    Eq << Eq[0] + z

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)


if __name__ == '__main__':
    run()
# created on 2021-04-12
