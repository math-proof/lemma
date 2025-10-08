from util import *


@apply
def apply(self):
    args = self.of(Sin[Piecewise])
    ecs = [(Sin(e), c) for e, c in args]
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)
    Eq << apply(Sin(Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.find(And).apply(Bool.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.find(And).apply(Bool.Cond.BFnIte.given.And_BFn, invert=True)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2023-04-30
