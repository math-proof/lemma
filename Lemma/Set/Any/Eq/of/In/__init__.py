from util import *


@apply(simplify=False)
def apply(given, reverse=False, var=None):
    lhs, rhs = given.of(Element)

    if var is None:
        x = given.generate_var(**rhs.etype.dict)
        limit = (x, rhs)
    else:
        if isinstance(var, str):
            x = given.generate_var(var=var, **rhs.etype.dict)
            limit = (x, rhs)
        else:
            x = var
            assert rhs in var.domain
            limit = (x,)

    if reverse:
        return Any(Equal(x, lhs), limit)
    return Any(Equal(lhs, x), limit)


@prove
def prove(Eq):
    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, S))

    Eq << Eq[1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-05-07

from . import split
