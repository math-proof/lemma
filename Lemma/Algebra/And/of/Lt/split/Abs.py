from util import *



@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, a = Symbol(integer=True, given=True)

    Eq << apply(abs(x) < a)

    Eq << Algebra.Lt.of.Lt.split.Abs.apply(Eq[0])

    Eq << -Algebra.Lt.of.Lt.split.Abs.apply(Eq[0], negate=True)


if __name__ == '__main__':
    run()
# created on 2019-12-28
