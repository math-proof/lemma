from util import *


@apply
def apply(x_given_z, y_given_z):
    (x, z), S[x] = x_given_z.of(Equal[Conditioned])
    (y, S[z]), S[y] = y_given_z.of(Equal[Conditioned])

    return Equal(Pr(x & y, given=z), Pr(x & y))


@prove(provable=False)
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | z, x), Equal(y | z, y))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Equal(Pr(x), 0))

    Eq << Logic.ImpAnd.of.Imp.cond.apply(Eq[0] & Eq[1], Eq[-1])






if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
