from util import *


@apply
def apply(self):
    ec = self.of(Piecewise)

    common_terms = None
    for e, c in ec:
        if e.is_Mul:
            if common_terms is None:
                common_terms = {*e.args}
            else:
                common_terms &= {*e.args}
        elif e.is_Zero:
            ...
        else:
            if common_terms is None:
                common_terms = {e}
            else:
                common_terms &= {e}
    if common_terms:
        args = []
        for e, c in self.args:
            if e.is_Mul:
                e = Mul(*{*e.args} - common_terms)
            elif e.is_Zero:
                ...
            else:
                e = 1
            args.append((e, c))
        rhs = Mul(*common_terms, Piecewise(*args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    r = Symbol(real=True, given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((r * g(x), Equal(x, y)), (r * f(x), Element(y, A)), (r * h(x), True)))

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(Logic.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].args[::2].apply(Logic.Cond.BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].args[:2].apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)

    Eq << Eq[-1].this.args[-1].args[::2].apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)

    Eq << Eq[-1].this.args[-1].args[:2].apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)

    Eq << Logic.Or_OrAndS.given.Or_And_Or.apply(Eq[-1], cond=Unequal(x, y), simplify=None)





if __name__ == '__main__':
    run()
# created on 2019-08-15
# updated on 2023-08-26
del Bool
from . import Bool
