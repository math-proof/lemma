from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    return Equal(x, S.Pi / 2 + S.Pi * Floor(x / S.Pi))


@prove
def prove(Eq):
    from Lemma import Set, Int, Real, Rat

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))

    Eq << Rat.Sub_Mul_FloorDiv.In.Ico.of.Gt_0.apply(x, S.Pi)

    Eq << Real.EqCosAddMul_Pi_0.of.EqCos_0.apply(Eq[0], -Floor(x / S.Pi))

    Eq << Real.Eq_DivPi2.of.EqCos_0.In_Icc0Pi.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-24

