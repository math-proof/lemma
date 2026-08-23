from util import *


def process_given_conditions(eq, f_eq, swap=False):
    if swap:
        f_eq, eq = eq, f_eq

    lhs, rhs = eq.of(Unequal)
    assert f_eq.is_Boolean

    return eq, f_eq._subs(KroneckerDelta(lhs, rhs), Zero())


@apply
def apply(ne, cond, **kwargs):
    eq, f_eq = process_given_conditions(ne, cond, **kwargs)
    return f_eq


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Unequal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))

    Eq << Equal(KroneckerDelta(x, y), 0, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[2].reversed


if __name__ == '__main__':
    run()

# created on 2020-07-18
