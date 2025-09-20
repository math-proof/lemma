from util import *


@apply
def apply(given):
    x_union, A = given.of(Equal[Intersection, EmptySet])
    if not x_union.is_Cup:
        x_union, A = A, x_union

    expr, *limits = x_union.of(Cup)
    return All(Equal(expr & A, A.etype.emptySet), *limits)


@prove
def prove(Eq):
    from Lemma import Set
    A = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k + 1,), etype=dtype.integer)

    Eq << apply(Equal(Cup[i:k](x[i]) & A, A.etype.emptySet))

    Eq << Eq[-1].simplify()

    Eq << Cup[i:k](x[i] & A).this.simplify()

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq << Eq[-1].apply(Set.All_Eq_Empty.Cup.of.Eq_Empty)


if __name__ == '__main__':
    run()

# created on 2020-08-10
