from util import *



@apply
def apply(given):
    et, fx = given.of(Given)
    eqs = et.of(And)
    return tuple(Given(eq, fx) for eq in eqs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Given(Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2]), Equal(f[n], g[n])))

    Eq << Eq[0].reversed

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].reversed

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-03-27
