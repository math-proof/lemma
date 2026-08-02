from util import *


@apply
def apply(x):
    from Lemma.Finset.H.eq.Add.definition import H
    from Lemma.Finset.K.eq.Add.definition import K

    n = x.shape[0]
    n -= 1
    assert x.is_positive
    assert n > 0
    return Equal(K(x[1:n + 1]) / H(x[1:n + 1]), H(x[:n + 1]) / K(x[:n + 1]) - x[0])


@prove
def prove(Eq):
    from Lemma import Bool
    from Lemma.Finset.Alpha.gt.Zero import alpha
    from Lemma import Finset
    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(x[:n + 1])

    Eq << Finset.Alpha.eq.DivH_K.positive.apply(alpha(x[:n + 1]))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Finset.Alpha.eq.DivH_K.positive.apply(alpha(x[1:n + 1]))

    Eq << Bool.UFn.of.UFn.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1] - x[0]


if __name__ == '__main__':
    run()

# created on 2020-09-25
