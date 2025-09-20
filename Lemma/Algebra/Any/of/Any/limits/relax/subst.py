from util import *


@apply
def apply(given, old, new):
    expr, [S[old]] = given.of(Any)
    assert old.domain in new.domain
    return Any[new](expr._subs(old, new))


@prove
def prove(Eq):
    from Lemma import Algebra
    a, b, z = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, right_open=True))
    y = Symbol(domain=Interval(a, b))
    f = Function(shape=(), integer=True)

    Eq << apply(Any[x](f(x) > 0), x, y)

    Eq << Eq[1].limits_subs(y, z)

    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], z, x)


if __name__ == '__main__':
    run()

# created on 2019-02-16
