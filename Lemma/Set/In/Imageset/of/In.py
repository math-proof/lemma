from util import *


@apply
def apply(given, f):
    x, s = given.of(Element)
    if x.is_given:
        z = s.generate_var(**x.type.dict)
        S = imageset(z, f(z), s)
    else:
        S = imageset(x, f(x), s)
    return Element(f(x), S)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool
    x = Symbol(integer=True)
    y = Symbol(integer=True, given=True)
    f = Function(integer=True)
    s = Symbol(etype=dtype.integer)

    Eq << apply(Element(y, s), f=f)

    S = Symbol(Eq[1].rhs)

    Eq << S.this.definition

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq.all_contains = All[x:s](Element(f(x), S), plausible=True)

    Eq << Eq.all_contains.this.expr.rhs.definition

    Eq << Eq[-1].this.expr.apply(Set.In.given.Subset, simplify=False)

    Eq << Set.All_Subset.given.Subset.lhs.apply(Eq[-1])

    Eq << Bool.Or_NotIn.of.All.apply(Eq.all_contains, x, y)

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-29
