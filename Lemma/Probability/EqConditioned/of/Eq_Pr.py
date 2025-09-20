from util import *


@apply
def apply(given, index=0):
    (joint, given), S[joint] = given.of(Equal[Pr[Conditioned], Pr])

    vars = []
    for cond in joint.of(And):
        x, x_var = cond.of(Equal)
        vars.append(x)

    v = vars[index]
    return Equal(v | given, v)


@prove
def prove(Eq):
    from Lemma import Probability

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(Pr(x & y | z), Pr(x, y)))

    Eq << Probability.And.Eq.Conditioned.of.Eq.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-03-23
# updated on 2023-03-24
