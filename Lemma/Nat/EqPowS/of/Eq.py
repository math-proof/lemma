from util import *


@apply
def apply(given, *, exp=None, base=None):
    lhs, rhs = given.of(Equal)
    if exp is not None:
        assert lhs > 0 or rhs > 0 or exp > 0
        return Equal(lhs ** exp, rhs ** exp)

    base = sympify(base)

    if base.is_integer:
        if lhs.is_integer:
            ...
        else:
            return
    else:
        if lhs > 0 or rhs > 0 or base > 0:
            ...
        else:
            return
    return Equal(base ** lhs, base ** rhs)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), integer=True)
    k = Symbol(real=True, positive=True)
    Eq << apply(Equal(f(i), g(i)), base=k)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-03-12

