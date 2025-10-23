from util import *


@apply
def apply(lt):
    i, l = lt.of(Less)
    return Equal(relu(i + 1 - l), 0)


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Nat

    i, l = Symbol(integer=True)
    Eq << apply(i < l)

    Eq << Eq[1].this.lhs.apply(Tensor.Relu.eq.Add.Min)

    Eq << Nat.LeAdd_1.of.Lt.apply(Eq[0])

    Eq << Nat.EqMin.of.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
