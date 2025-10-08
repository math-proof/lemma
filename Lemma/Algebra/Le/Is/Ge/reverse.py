from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    return GreaterEqual(a, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a = Symbol(real=True, given=True)
    Eq << apply(x <= a)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-11-26
