from util import *


@apply
def apply(self, indices, wrt=None, *, simplify=True):
    from Lemma.Finset.Sum.eq.AddSumS import split
    return Equal(self, split(Cap, self, indices, wrt=wrt, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(integer=True)
    f = Function(etype=dtype.real)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Cap[x:A](f(x)), B)

    return # the following will result recursive proving
    Eq << Set.eq.of.suffice.apply(Eq[0], wrt='y')
    Eq <<= Eq[-2].this.rhs.apply(Set.element.of.contains.split.intersection, simplify=False), \
    Eq[-1].this.lhs.apply(Set.element.then.contains.split.intersection)
    Eq <<= Eq[-2].this.lhs.apply(Set.element.then.All_contains.st.Cap), \
    Eq[-1].this.rhs.apply(Set.element.of.All_contains.st.Cap)
    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.element.of.All_contains.st.Cap), \
    Eq[-1].this.lhs.args[0].apply(Set.element.then.All_contains.st.Cap)
    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.element.of.All_contains.st.Cap), \
    Eq[-1].this.lhs.args[0].apply(Set.element.then.All_contains.st.Cap)
    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.all.of.all.limits_union), \
    Eq[-1].this.lhs.apply(Algebra.All.all.then.all.limits_union)


if __name__ == '__main__':
    run()

# created on 2021-01-19
