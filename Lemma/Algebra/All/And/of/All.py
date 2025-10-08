from util import *


@apply(simplify=False)
def apply(given, index=None):
    from sympy.concrete.limits import limits_cond
    fn, *limits = given.of(ForAll)

    if index is None:
        cond = limits_cond(limits)
    else:
        if isinstance(index, slice):
            cond = limits_cond(limits[index])
        else:
            cond = limits_cond([limits[index]])
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(ForAll[x:g(x) > 0](f(x) > 0))

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-17

