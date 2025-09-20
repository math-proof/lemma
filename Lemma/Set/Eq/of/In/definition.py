from util import *


@apply
def apply(given, var=None):
    lhs, rhs = given.of(Element)

    if var is None:
        x = given.generate_var(domain=rhs, definition=lhs)
    else:
        assert isinstance(var, str)
        x = given.generate_var(var=var, domain=rhs, definition=lhs)
    
    return Equal(x, lhs)


@prove
def prove(Eq):
    x = Symbol(real=True)
    S = Symbol(etype=dtype.integer)
    f = Function(real=True)
    Eq << apply(Element(f(x), S), 'w')

    Eq << Eq[1].reversed

    


if __name__ == '__main__':
    run()
# created on 2023-04-17
