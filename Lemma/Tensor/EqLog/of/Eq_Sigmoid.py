from util import *


@apply
def apply(given):
    x, y = given.of(Equal[sigmoid])

    return Equal(x, log(y / (1 - y)))


@prove
def prove(Eq):
    from Lemma import Bool, Rat, Real

    x, y = Symbol(real=True)
    Eq << apply(Equal(y, sigmoid(x)))

    Eq << Eq[0].this.rhs.defun()

    Eq << Rat.EqInv.of.Eq.apply(Eq[-1])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.lhs.apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    Eq << Bool.UFn.of.Eq.apply(Eq[-1], log)

    Eq << -Eq[-1]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.rhs.apply(Real.Mul.eq.Log)


if __name__ == '__main__':
    run()
# created on 2023-10-06
