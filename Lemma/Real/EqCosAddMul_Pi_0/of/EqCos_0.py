from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    if n is None:
        n = is_zero.generate_var(integer=True, var='n')

    return Equal(cos(x + n * S.Pi), 0)


@prove
def prove(Eq):
    from Lemma import Bool, Real

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))

    Eq << Real.EqCosSub_Mul_Pi0.of.EqCos_0.apply(Eq[0])

    Eq << Real.EqCosSub_Mul_Pi0.of.EqCos_0.apply(Eq[0], negative=True)

    Eq << Eq[-1].this.apply(Bool.All.Is.All_UFnSub, Eq[-1].variable, -Eq[-1].variable)
    Eq <<= Eq[-1] & Eq[-3]

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-21
