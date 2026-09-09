from util import *


@apply
def apply(given, index=-1):
    args, rhs = given.of(Equal[FiniteSet])

    first = args[:index]
    second = args[index:]

    first = [Element(lhs, rhs).simplify() for lhs in first]
    second = [Element(lhs, rhs).simplify() for lhs in second]

    return And(*first), And(*second)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Equal({a, b}, S))



    Eq << Element(a, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Element(b, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-08-28
