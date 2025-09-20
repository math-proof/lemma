from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << Algebra.And.Lt.of.Lt_Min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-03
