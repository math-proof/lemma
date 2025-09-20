from util import *


@apply
def apply(ne, *vars):
    given = []
    rest = []
    vars = [*vars]

    args = ne.of(Unequal[Pr[And], 0])
    if args[-1].is_Tuple:
        args, *weights = args
    else:
        weights = []

    for cond in args:
        x, x_var = cond.of(Equal)
        if x in vars:
            rest.append(cond)
            vars.remove(x)
        else:
            given.append(cond)

    rest = And(*rest)
    given = And(*given)
    joint = And(*(Equal(x, x.var) for x in vars))
    return Equal(Pr(joint & rest, *weights, given=given), Pr(rest, *weights, given=given) * Pr(joint, *weights, given=rest & given))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(y, z), 0), x, y)

    Eq << Probability.Ne_0.Conditioned.of.Ne_0.apply(Eq[0], z)

    Eq << Probability.Eq.of.Ne_0.bayes.Conditioned.apply(Eq[-1], x)



if __name__ == '__main__':
    run()
# created on 2023-03-27
