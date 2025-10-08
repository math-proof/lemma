from util import *


@apply
def apply(ne_zero, z_given_x, z_given_y):
    x, y = ne_zero.of(Unequal[Pr[And], 0])
    (z, S[x]), S[z] = z_given_x.of(Equal[Conditioned])
    (S[z], S[y]), S[z] = z_given_y.of(Equal[Conditioned])
    return Equal(z | x & y, z)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Bool

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(x, y), 0), Equal(z | x, z), Equal(z | y, z))



    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq[0], Eq[1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-04-05
