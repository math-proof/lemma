from util import *


@apply
def apply(self, additive=None):
    ec = self.of(Piecewise)

    if additive is None:
        common_terms = None
        for e, c in ec:
            if e.is_Add:
                if common_terms is None:
                    common_terms = {*e.args}
                else:
                    common_terms &= {*e.args}
            else:
                if common_terms is None:
                    common_terms = {e}
                else:
                    common_terms &= {e}
        if common_terms:
            args = []
            for e, c in self.args:
                if e.is_Add:
                    e = Add(*{*e.args} - common_terms)
                else:
                    e = Zeros(*e.shape)
                args.append((e, c))
            rhs = Add(*common_terms, Piecewise(*args))

    else:
        ec = [(e + additive, c)for e, c in ec]
        rhs = Add(Piecewise(*ec), -additive)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    z = Symbol(real=True, shape=(), given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Equal(x, y)), (f(x), Element(y, A)), (h(x), True)), z)

    Eq << Eq[-1] + z

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(Bool.And_BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].args[::2].apply(Bool.And_BFnIte.given.And_BFn)

    Eq << Eq[-1].this.args[1].args[:2].apply(Bool.And_BFnIte.given.And_BFn, invert=True)

    Eq << Eq[-1].this.args[-1].args[::2].apply(Bool.And_BFnIte.given.And_BFn, invert=True)

    Eq << Eq[-1].this.args[-1].args[:2].apply(Bool.And_BFnIte.given.And_BFn, invert=True)

    Eq << Bool.Or_OrAndS.given.Or_And_Or.apply(Eq[-1], cond=Unequal(x, y), simplify=None)





if __name__ == '__main__':
    run()
# created on 2018-02-22
# updated on 2023-05-20
