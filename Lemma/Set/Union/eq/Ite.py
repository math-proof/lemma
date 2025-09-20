from util import *


@apply
def apply(self):
    [*args] = self.of(Union)
    for i, piecewise in enumerate(args):
        if piecewise.is_Piecewise:
            del args[i]
            break
    else:
        return

    s = Union(*args)

    ecs = ((e | s, c) for e, c in piecewise.args)
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(integer=True)
    f, g, h, t = Function(etype=dtype.real)
    Eq << apply(Union(Piecewise((f(x), x > 0), (g(x), True)), h(x), t(x), evaluate=False))

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Logic.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)





if __name__ == '__main__':
    run()

# created on 2021-01-24
# updated on 2023-05-09
