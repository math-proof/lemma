from util import *


@apply
def apply(self, y):
    fx, (x, x0) = self.of(Limit)
    assert not self._has(y)
    assert y.is_symbol and not y.is_given
    fy = fx._subs(x, y)

    return Equal(self, Limit[y:x0](fy))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Bool

    x, y, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Limit[x:x0](f(x)), y)

    # we assume this limit exists and is real
    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.expr.limits_subs(Eq[-1].expr.variable, x)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-04-06
