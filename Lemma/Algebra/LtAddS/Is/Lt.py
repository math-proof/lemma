from util import *


@apply
def apply(given):
    from Lemma.Algebra.EqAddS.Is.Eq import simplify_common_terms
    return simplify_common_terms(Less, given)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)


    Eq << apply(Less(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
# created on 2018-10-10
