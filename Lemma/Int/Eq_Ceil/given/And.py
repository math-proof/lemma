from util import *


@apply
def apply(given):
    y, fx = given.of(Equal)
    if not fx.is_Ceil:
        y, fx = fx, y
    assert y.is_integer
    x = fx.of(Ceil)
    return x + 1 > y, y >= x


@prove
def prove(Eq):
    from Lemma import Int

    x = Symbol(real=True)
    y = Symbol(integer=True)
    Eq << apply(Equal(y, ceil(x)))



    Eq <<= -Eq[-2], -Eq[-1]

    Eq << Int.Eq.of.Lt.Le.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Int.Floor.eq.NegCeilNeg)


if __name__ == '__main__':
    run()
# created on 2019-03-08
