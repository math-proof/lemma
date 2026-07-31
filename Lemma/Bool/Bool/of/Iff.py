from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Iff)
    return Equal(Bool(fn), Bool(fn1))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int, Int

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Iff(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Bool.Imp.of.Iff.apply(Eq[0])

    Eq << Bool.Bool.eq.MulBoolS.of.Imp.apply(Eq[-1])

    Eq << Bool.Imp.of.Iff.apply(Eq[0], reverse=True)

    Eq << Bool.Bool.eq.MulBoolS.of.Imp.apply(Eq[-1])

    Eq << Eq[-1] - Eq[-3]

    Eq << Int.Eq.of.Sub.eq.Zero.apply(Eq[-1], reverse=True)





if __name__ == '__main__':
    run()

# created on 2018-01-29
# updated on 2025-04-12
