from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    return Equal(x, S.Pi / 2 + S.Pi * Floor(x / S.Pi))


@prove
def prove(Eq):
    from Lemma import Set, Trigonometry, Algebra, Int

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))

    Eq << Set.Sub_Mul_FloorDiv.In.Ico.apply(x, S.Pi)

    Eq << Trigonometry.Cos.eq.Zero.of.Cos.eq.Zero.apply(Eq[0], -Floor(x / S.Pi))

    Eq << Trigonometry.Eq.of.Cos.eq.Zero.In.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-24

from . import In
