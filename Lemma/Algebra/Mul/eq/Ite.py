from util import *


@apply
def apply(self, *, simplify=True):
    [*args] = self.of(Mul)
    for i, rhs in enumerate(args):
        if rhs.is_Piecewise:
            break
    else :
        return

    del args[i]
    delta = Mul(*args, evaluate=False)

    if not delta.is_One:
        rhs = Piecewise(*((e * delta, c) for e, c in rhs.args))

    if simplify:
        rhs = rhs.simplify()
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Piecewise((g(x), x > 0), (h(x), True)) * y)

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Bool.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].apply(Bool.Cond.BFnIte.given.And_BFn, invert=True)


if __name__ == '__main__':
    run()
# created on 2022-01-23


# updated on 2023-05-20
