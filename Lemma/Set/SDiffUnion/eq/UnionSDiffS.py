from util import *


@apply
def apply(complement, evaluate=True):
    union, C = complement.of(Complement)
    union = union.of(Union)
    return Equal(complement, Union(*(u - C for u in union), evaluate=evaluate))


@prove
def prove(Eq):
    from Lemma import Set
    B, A, C = Symbol(etype=dtype.integer)

    Eq << apply((A | B) - C, evaluate=False)

    A = Symbol(A - C)
    B = Symbol(B - C)

    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition

    Eq << Set.EqUnionS.of.Eq.Eq.apply(Eq.A_definition, Eq.B_definition)

    Eq << Eq[0].this.rhs.subs(Eq.A_definition.reversed, Eq.B_definition.reversed)

    Eq << Eq[-1].subs(Eq[1])

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


if __name__ == '__main__':
    run()

# created on 2018-01-08
