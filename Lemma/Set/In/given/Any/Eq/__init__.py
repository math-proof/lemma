from util import *


@apply(simplify=False)
def apply(imply, var=None):
    lhs, rhs = imply.of(Element)
    if var is None:
        var = imply.generate_var(**lhs.type.dict)
    elif isinstance(var, str):
        var = imply.generate_var(var=var, **rhs.etype.dict)

    return Any[var:rhs](Equal(lhs, var))


@prove
def prove(Eq):
    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, S))

    Eq << Eq[1].simplify()





if __name__ == '__main__':
    run()

# created on 2021-07-26

# updated on 2022-04-03


from . import split
