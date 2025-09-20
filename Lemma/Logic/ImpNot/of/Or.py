from util import *


@apply
def apply(given, pivot=0):
    [*conds] = given.of(Or)

    if isinstance(pivot, tuple):
        eq = []
        for i in sorted(pivot, reverse=True):
            eq.append(conds.pop(i))
        eq = Or(*eq)
    else:
        eq = conds.pop(pivot)

    cond = eq.invert()

    return Imply(cond, given.func(*conds))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(complex=True, shape=(n,))
    f, g = Function(complex=True, shape=())
    Eq << apply(Unequal(f(x), 1) | Unequal(g(x), 1) | Equal(x, y), pivot=(0, 1))

    Eq << Eq[1].apply(Logic.Imp.given.Or_Not)


if __name__ == '__main__':
    run()

# created on 2018-03-21
