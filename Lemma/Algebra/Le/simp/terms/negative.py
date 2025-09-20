from util import *


@apply
def apply(given):
    from Lemma.Algebra.Eq.simp.terms.negative import simplify_negative_terms
    return simplify_negative_terms(LessEqual, given)


@prove
def prove(Eq):
    x, y, a, b = Symbol(real=True)

    Eq << apply(LessEqual(x - a, y - b))

    Eq << Eq[-1].this.lhs + a

    Eq << Eq[-1].this.lhs + b


if __name__ == '__main__':
    run()

# created on 2021-09-14
