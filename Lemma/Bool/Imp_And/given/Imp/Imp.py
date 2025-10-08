from util import *


@apply
def apply(given, index=-1):
    cond, et = given.of(Imply)
    eqs = et.of(And)
    if index is not None:
        first = And(*eqs[:index])
        second = And(*eqs[index:])
        return Imply(cond, first), Imply(cond, second)
    return tuple((Imply(cond, eq) for eq in eqs))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n, x, y = Symbol(integer=True, nonnegative=True)
    f, g, h = Function(integer=True)
    Eq << apply(Imply(x > y, (f(x) > g(y)) & (f(x) > h(y))))

    Eq << Eq[0].apply(Bool.Imp.given.Or_Not)

    Eq << Bool.Or.of.ImpNot.apply(Eq[1])

    Eq << Bool.Or.of.ImpNot.apply(Eq[2])

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()


# created on 2018-02-01
