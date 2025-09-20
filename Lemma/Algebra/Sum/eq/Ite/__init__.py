from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    variables = self.variables

    for _, cond in expr.of(Piecewise):
        assert not cond.has(*variables)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in expr.of(Piecewise)]

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i, j = Symbol(integer=True)
    x, y = Symbol(integer=True, given=True)
    A, B, C, D = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True)
    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Element(x, A & B)), (h(i, j), True))))

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Logic.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)







if __name__ == '__main__':
    run()


# created on 2020-03-17
# updated on 2023-08-26
from . import pop
from . import unshift
