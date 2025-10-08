from util import *


@apply
def apply(self, lower=True, upper=None):
    x, [l], [u] = self.of(BandPart)
    n, m = x.shape
    if lower:
        l = Min(l, n - 1)

    if upper:
        u = Min(u, m - 1)

    return Equal(self, BandPart[l, u](x))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Tensor

    m, n, l, u = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, m), real=True)
    Eq << apply(BandPart[l, u](x))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].this.rhs.defun()

    i = Symbol(domain=Range(n))
    j = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], (i, j))

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Ico.Is.And)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Ico.Is.And)

    Eq << Eq[-1].this.find(-Min).apply(Algebra.Mul.eq.Max)

    Eq << Eq[-1].this.find(Add >= Max).apply(Algebra.Ge_Max.Is.And.Ge)




if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-01-23
