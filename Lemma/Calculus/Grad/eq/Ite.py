from util import *


@apply
def apply(self, *, simplify=True):
    ecs, *limits_d = self.of(Derivative[Piecewise])

    args = []
    for expr, cond in ecs:
        expr = Derivative(expr, *limits_d)

        if simplify:
            expr = expr.doit()

        args.append((expr, cond))


    return Equal(self, Piecewise(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Bool.And_BFnIte.given.And_BFn)

    Eq << Eq[-1].this.find(And).apply(Bool.And_BFnIte.given.And_BFn, invert=True)





if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-05-20
