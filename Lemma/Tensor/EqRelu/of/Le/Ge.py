from util import *


@apply
def apply(le, ge):
    k, n = le.of(LessEqual)
    S[k], min_mn = ge.of(GreaterEqual)
    [*args] = min_mn.of(Min)
    index = args.index(n)
    del args[index]
    m = Min(*args)
    return Equal(k - min_mn, relu(k - m))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    k, n, m = Symbol(integer=True)
    Eq << apply(k <= n, k >= Min(m, n))

    Eq << Eq[-1].this.rhs.apply(Tensor.Relu.eq.Add.Min)

    Eq << Algebra.EqMin.of.Le.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Algebra.EqMin.of.Ge.apply(Eq[1]).reversed





if __name__ == '__main__':
    run()
# created on 2021-12-25
