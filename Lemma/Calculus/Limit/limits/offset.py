from util import *


@apply
def apply(self, offset):
    fx, (x, x0) = self.of(Limit)
    fx = fx._subs(x, x + offset)

    return Equal(self, Limit[x:x0 - offset](fx))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Logic

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Limit[x:x0](f(x - x0)), x0)

    # we assume this limit exists and is real
    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.AllIn_Ico.of.AllIn_Ico.offset, -x0)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-04-05
