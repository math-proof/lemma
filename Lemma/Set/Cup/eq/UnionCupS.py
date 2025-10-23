from util import *


@apply
def apply(self, *, cond, wrt=None, simplify=True):
    from Lemma.Finset.Sum.eq.AddSumS import split
    return Equal(self, split(Cup, self, cond, wrt=wrt, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(integer=True)
    f = Function(etype=dtype.real)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Cup[x:A](f(x)), cond=B)

    return # the following will result in recursive proving!
    Eq << Set.eq.of.suffice.apply(Eq[0], wrt='y')
    Eq <<= Eq[-2].this.rhs.apply(Set.element.of.ou.split.Union), \
    Eq[-1].this.lhs.apply(Set.element.then.ou.split.Union)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(Set.element.then.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(Set.element.of.any_contains.st.cup)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(Set.element.of.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(Set.element.then.any_contains.st.cup)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(Set.element.of.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(Set.element.then.any_contains.st.cup)
    Eq <<= Eq[-2].this.rhs.apply(Algebra.ou.of.any), \
    Eq[-1].this.lhs.apply(Algebra.ou.then.any)


if __name__ == '__main__':
    run()

# created on 2018-09-01
