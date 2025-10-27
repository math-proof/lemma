from util import *


@apply
def apply(x):
    return Greater(Floor(x), x - 1)


@prove(provable=False)
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    return
    Eq << Algebra.Floor.to.maxima.apply(Eq[0].lhs)

    y = Symbol(Eq[1].lhs)
    Eq << y.this.definition

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Algebra.eq_maxima.then.All_Ge.apply(Eq[-1])

    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << ~Eq[-1]

    Eq << Algebra.Cond.all.then.All_And.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.apply(Algebra.le.ge.then.le.transit)

    Eq << ~Eq[-1]

    Eq << Algebra.any.of.Any_And.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.gt.le.of.el)

    n = Eq[-1].variable
    Eq << Set.then.any_el.integer.apply(x, n)


if __name__ == '__main__':
    run()

# created on 2018-03-02
