from util import *


@apply
def apply(self):
    assert self.is_ConditionSet
    variable, expr, base_set = self.base_set.image_set()
    if base_set.is_bool:
        condition = base_set & self.condition._subs(self.variable, expr)
    else:
        condition = Element(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
    return Equal(self, imageset(variable, expr, conditionset(variable, condition)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Nat

    n, m = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    y = Symbol(complex=True, shape=(m,))
    A = Symbol(etype=dtype.complex[n])
    f = Function(complex=True, shape=(m,))
    g = Function(shape=(), real=True)
    s = Symbol(imageset(x, f(x), A))
    Eq << apply(conditionset(y, g(y) > 0, s))

    Eq << Eq[1].this.lhs.limits[0][2].definition

    B = Symbol(Eq[-1].lhs)
    B_quote = Symbol(Eq[-1].rhs)
    Eq << B.this.definition

    Eq << B_quote.this.definition

    Eq.suffice = Imply(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.suffice.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Set.In.given.Any.Eq.split.Imageset)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Bool.AnySetOf.given.Any_And)

    Eq << Eq[-1].this.lhs.args[1].apply(Set.Any.Eq.of.In.split.Imageset)

    Eq << Eq[-1].this.rhs.expr.apply(Nat.Eq.UFn.given.Eq.UFn, reverse=True)

    Eq.necessary = Given(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.necessary.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Set.Any.Eq.of.In.split.Imageset)

    Eq << Eq[-1].this.rhs.apply(Bool.Any_And.of.AnySetOf)

    Eq << Eq[-1].this.rhs.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True, ret=0)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.lhs.args[1].apply(Set.In.given.Any.Eq.split.Imageset)

    Eq << Set.Eq.of.ImpIn.ImpIn.apply(Eq.suffice, Eq.necessary)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition





if __name__ == '__main__':
    run()

# created on 2021-02-04
# updated on 2023-11-11
