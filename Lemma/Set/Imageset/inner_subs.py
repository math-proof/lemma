from util import *


@apply
def apply(self):
    expr, (x, et) = self.of(Cup[FiniteSet])
    if et.is_ConditionSet:
        et = et.condition & Element(x, et.base_set)
    if et.is_And:
        eqs = et._argset
    else:
        eqs = {et}

    for eq in eqs:
        if eq.is_Equal:
            return Equal(self, imageset(x, expr._subs(*eq.args), et).simplify())


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    n, m = Symbol(integer=True, positive=True)

    x = Symbol(complex=True, shape=(n,))
    f, g = Function(complex=True, shape=(m,))

    h = Function(shape=(), real=True)

    Eq << apply(imageset(x, f(x), Equal(f(x), g(x)) & (h(x) > 0)))

    Eq << Eq[0].this.lhs.apply(Set.Cup.eq.Cup_Ite)

    Eq << Eq[-1].this.lhs.expr.apply(Logic.Ite.subst)


if __name__ == '__main__':
    run()

# created on 2020-07-10
