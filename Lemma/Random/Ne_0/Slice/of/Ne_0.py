from util import *


@apply
def apply(ne_zero, index):
    lhs, rhs = ne_zero.of(Unequal[Pr[Equal], 0])

    return Unequal(Pr(Equal(lhs[index], rhs[index])), 0)


@prove
def prove(Eq):
    from Lemma import Random, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(real=True, shape=(n,), random=True)
    t = Symbol(domain=Range(1, n))
    Eq << apply(Unequal(Pr(x), 0), slice(0, t))

    t = Symbol(domain=Range(1, n))
    Eq << Eq[0].this.lhs.arg.apply(Tensor.GetSlice.Get.of.Eq, t)

    Eq << Random.NePr_0.NePr_0.of.NePr__0.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-07-23
# updated on 2023-03-26
