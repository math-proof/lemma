from util import *


@apply(simplify=False)
def apply(given):
    (x, y), *limits = given.of(Any[Equal])
    cond = given.limits_cond
    return cond._subs(x, y)


@prove
def prove(Eq):
    x, y = Symbol(integer=True)

    S = Symbol(etype=dtype.integer)

    Eq << apply(Any[x:S](Equal(x, y)))

    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()

# created on 2021-08-09
