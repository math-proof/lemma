from util import *


@apply
def apply(self, lower=None, upper=None, strict=False):
    assert not self.shape
    if upper is not None:
        assert not upper.shape
        if strict:
            rhs = Piecewise((Min(self, upper), upper > self), (Max(self, upper), True))
        else:
            rhs = Piecewise((Min(self, upper), upper >= self), (Max(self, upper), True))
    elif lower is not None:
        assert not lower.shape
        if strict:
            rhs = Piecewise((Max(self, lower), lower < self), (Min(self, lower), True))
        else:
            rhs = Piecewise((Max(self, lower), lower <= self), (Min(self, lower), True))

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a = Symbol(real=True)
    Eq << apply(x, upper=a)

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Ite)

    Eq << Eq[-1].this.args[0].apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)

    Eq << Eq[-1].this.find(Min).apply(Algebra.Min.eq.IteLt)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.BFnIte.given.And_BFn, invert=True)





if __name__ == '__main__':
    run()
# created on 2021-12-23
# updated on 2023-05-20
