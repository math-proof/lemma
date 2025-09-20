from util import *


@apply
def apply(given, q=None):
    mod, r = given.of(Equal)
    n, d = mod.of(Mod)
    if q is None:
        q = Symbol(integer=True)

    return Any[q](Equal(n, q * d + r))


@prove
def prove(Eq):
    from Lemma import Algebra
#     n = q * d + r
    n, d = Symbol(integer=True, given=True)


    r = Symbol(integer=True)

    Eq << apply(Equal(n % d, r))

    Eq << Eq[0].this.lhs.apply(Algebra.Mod.eq.Sub_Mul_Div)

    Eq << Eq[-1] + n // d * d

    q = Eq[1].variable

    Eq << Algebra.Any.given.Cond.subst.apply(Eq[1], q, n // d)


if __name__ == '__main__':
    run()
# created on 2018-05-03
