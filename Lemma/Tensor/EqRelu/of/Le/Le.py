from util import *


@apply
def apply(le_min, le):
    min_mn, k = le_min.of(LessEqual)
    S[k], n = le.of(LessEqual)

    [*args] = min_mn.of(Min)
    index = args.index(n)
    del args[index]
    m = Min(*args)
    return Equal(k - min_mn, relu(k - m))


@prove
def prove(Eq):
    from Lemma import Tensor

    k, n, m = Symbol(integer=True)
    Eq << apply(Min(m, n) <= k, k <= n)

    Eq << Tensor.EqRelu.of.Le.Ge.apply(Eq[1], Eq[0].reversed)



if __name__ == '__main__':
    run()
# created on 2021-12-25
