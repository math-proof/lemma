from util import *


@apply
def apply(given):
    from Lemma.Nat.EqAddS.Is.Eq import simplify_common_terms
    return simplify_common_terms(Unequal, given)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, a = Symbol(real=True, shape=(n,))


    Eq << apply(Unequal(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
# created on 2020-02-03
