from util import *


@apply(simplify=False)
def apply(limits):
    from sympy.concrete.limits import limits_cond
    return All(limits_cond(limits), *limits)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    f = Any[x: Interval(0, n)](Equal(x * 2, 1))

    Eq << apply(f.limits)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2019-05-09
