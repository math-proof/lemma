from util import *



@apply
def apply(given, negate=False):
    x, M = given.of(Less)
    x = x.of(Abs)
    if negate:
        x = -x
    return Less(x, M)


@prove
def prove(Eq):
    from Lemma import Algebra
    M, a = Symbol(real=True)

    Eq << apply(Less(abs(a), M), negate=True)

    Eq << Algebra.Le_Abs.apply(a, negate=True)

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-12-27
