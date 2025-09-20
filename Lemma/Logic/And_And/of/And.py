from util import *


def split(given, index):
    eqs = given.of(And)

    if index is None:
        return eqs
    lhs, rhs = std.array_split(eqs, index)
    return And(*lhs), And(*rhs)


@apply
def apply(given, index=-1):
    return split(given, index)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)), index=slice(1, 3))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq << Imply(Eq[0], Eq[2], plausible=True)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()


# created on 2018-01-04
# updated on 2023-04-24
