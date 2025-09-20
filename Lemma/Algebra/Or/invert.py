from util import *


@apply
def apply(given, i=-1, j=None):
    [*args] = given.of(Or)
    if i < 0:
        i += len(args)
    if j is None:
        j = i - 1

    pivot = args[i]
    conj = pivot.invert()
    args[j] &= conj

    return Or(*args)

@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(Greater(x, y) | Greater(a, b))



    Eq << Eq[-1].this.rhs.apply(Algebra.Or.Is.And)





if __name__ == '__main__':
    run()
# created on 2021-12-17
