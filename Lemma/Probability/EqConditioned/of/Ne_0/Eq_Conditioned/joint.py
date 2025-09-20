from util import *


@apply
def apply(ne, eq):
    [*conds] = ne.of(Unequal[Pr[And], 0])
    lhs, x = eq.of(Equal)
    if lhs.is_Probability:
        x = x.of(Pr)
        lhs = lhs.arg

    S[x], given = lhs.of(Conditioned)

    if given.is_And:
        for g in given.args:
            del conds[conds.index(g)]
    else:
        del conds[conds.index(given)]

    z = And(*conds)
    if x.is_symbol:
        return Equal(x | given & z, x | z)
    else:
        return Equal(Pr(x, given=given & z), Pr(x, given=z))


@prove(provable=False)
def prove(Eq):
    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(y, z), 0), Equal(x | y, x))

    
    


if __name__ == '__main__':
    run()
# created on 2020-12-16
# updated on 2023-04-05

