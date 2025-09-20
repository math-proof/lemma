from util import *


@apply
def apply(lt):
    i, l = lt.of(Less)
    return Equal(relu(i + 1 - l), 0)


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    i, l = Symbol(integer=True)
    Eq << apply(i < l)

    Eq << Eq[1].this.lhs.apply(Tensor.Relu.eq.Add.Min)

    Eq << Algebra.Le.of.Lt.strengthen.plus.apply(Eq[0])

    Eq << Algebra.EqMin.of.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
