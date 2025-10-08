from util import *


@apply
def apply(given, index):
    from Lemma.Bool.AnySetOf.of.Any_And import limits_absorb
    return limits_absorb(given, index)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    f, g, h = Function(shape=(), integer=True)
    f_quote = Function(shape=(), integer=True)
    Eq << apply(Any[x[:n]:f(x[:n]) > 0, x[n]]((g(x[n]) > f_quote(x[:n])) & (h(x[:n + 1]) > 0)), index=0)

    Eq << Bool.Any_And.of.AnySetOf.apply(Eq[1])

    Eq << Bool.AnySetOf.given.Any_And.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-10-02
