from util import *


@apply
def apply(given):
    from Lemma.Algebra.EqAddS.Is.Eq import simplify_common_terms
    return simplify_common_terms(GreaterEqual, given)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)


    Eq << apply(GreaterEqual(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
# created on 2019-05-15
