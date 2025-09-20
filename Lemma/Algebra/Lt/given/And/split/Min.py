from util import *



@apply
def apply(given):
    x, max_ab = given.of(Less)
    ab = max_ab.of(Min)
    return tuple(x < a for a in ab)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, a, b = Symbol(integer=True, given=True)

    Eq << apply(x < Min(a, b))

    Eq << Algebra.LtMin.of.Lt.Lt.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
# created on 2019-12-16
