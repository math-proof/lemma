from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R == Reals - {0}
    assert x.is_complex
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Complex

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << ~Eq[1]

    Eq << GreaterEqual(abs(x), 0, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Complex.Eq_0.of.EqNorm_0.apply(Eq[-1])

    Eq << Bool.Cond.of.Eq.Cond.subst.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-03-11
