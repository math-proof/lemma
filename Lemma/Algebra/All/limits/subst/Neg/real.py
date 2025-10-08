from util import *


def limits_subs(All, self, old, new):
    expr, (i, *ab) = self.of(All)
    assert not i.is_integer
    assert old == i

    c = new + i
    if len(ab) == 2:
        a, b = ab
        limit = (i, c - b, c - a)
    else:
        ab, = ab
        a, b = ab.of(Interval)
        limit = (i, Interval(c - b, c - a, **ab.kwargs_reversed))

    assert not c._has(i)
    return All(expr._subs(old, new), limit)

@apply
def apply(self, old, new):
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.of.All.limits.subst.Neg.real, x, c - x)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.subst.Neg.real, x, c - x)








if __name__ == '__main__':
    run()
# created on 2018-12-20
