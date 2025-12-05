from util import *


@apply
def apply(self, *, simplify=True):
    ecs = self.of(Ceil[Piecewise])
    ecs = [(Ceil(e), c) for e, c in ecs]

    return Equal(self, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Ceil(Piecewise((g(x), x > 0), (h(x), True))))

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Bool.And_BFnIte.given.And_BFn)

    Eq << Eq[-1].this.find(And).apply(Bool.And_BFnIte.given.And_BFn, invert=True)





if __name__ == '__main__':
    run()
# created on 2018-11-02
# updated on 2023-05-20
