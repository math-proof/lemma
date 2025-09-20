from util import *


@apply
def apply(self, *, simplify=True):
    ecs = self.of(Arg[Piecewise])
    ecs = [(Arg(e), c) for e, c in ecs]

    return Equal(self, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Arg(Piecewise((g(x), x > 0), (h(x), True))))

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Logic.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)





if __name__ == '__main__':
    run()
# created on 2018-11-01
# updated on 2023-05-18
