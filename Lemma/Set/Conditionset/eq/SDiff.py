from util import *

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(a, wrt=None):
    if wrt is None:
        wrt = a.generate_var(**a.type.dict)
    U = a.universalSet
    return Equal(conditionset(wrt, Unequal(wrt, a)), U - a.set)


@prove
def prove(Eq):
    from Lemma import Set, Algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))

    Eq << apply(x)

    A = Symbol(Eq[0].lhs)
    B = Symbol(Eq[0].rhs)

    a = Eq[0].lhs.variable
    Eq.all_contains_in_B = All[a:A](Element(a, B), plausible=True)

    Eq << Eq.all_contains_in_B.this.limits[0][1].definition

    Eq << Eq[-1].this.expr.rhs.definition

    Eq.all_contains_in_A = All[a:B](Element(a, A), plausible=True)

    Eq << Eq.all_contains_in_A.this.limits[0][1].definition

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << All[a:Eq[-1].expr.invert()](Eq[-1].limits_cond.invert(), plausible=True)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Algebra.All.of.All.limits.invert.apply(Eq[-1])

    Eq << Set.Eq.of.All_In.All_In.apply(Eq.all_contains_in_A, Eq.all_contains_in_B)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-02-04
