from util import *


@apply
def apply(ne, eq):
    z, _y = ne.of(Unequal[Pr[Conditioned], 0])

    lhs, x = eq.of(Equal)
    if lhs.is_Probability:
        lhs = lhs.arg
        x = x.of(Pr)

    S[x], y = lhs.of(Conditioned)

    if _y != y:
        _y, z = z, _y

    assert _y == y

    if x.is_bool:
        return Equal(Pr(x, given=y & z), Pr(x, given=z))
    return Equal(x | y & z, x | z)


@prove
def prove(Eq):
    from Lemma import Probability

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(z | y), 0), Equal(x | y, x))

    Eq << Probability.Ne_0.of.Ne_0.joint.apply(Eq[0])

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq[-1], Eq[1])



if __name__ == '__main__':
    run()
# created on 2020-12-15
# updated on 2023-04-02
