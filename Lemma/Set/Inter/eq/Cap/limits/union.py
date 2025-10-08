from util import *


@apply
def apply(self):
    A, B = self.of(Intersection)
    function, *limits_a = A.of(Cap)
    S[function], *limits_b = B.of(Cap)
    from Lemma.Set.Union.eq.Cup.limits.Union import limits_union
    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Cap(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:A](f(k)), Cap[k:B](f(k)), evaluate=False))

    Eq << Eq[0].this.find(Cap).apply(Set.Cap.eq.Cap_Ite)

    Eq << Eq[-1].this.lhs.find(Cap).apply(Set.Cap.eq.Cap_Ite)

    Eq << Eq[-1].this.lhs.find(Cap).apply(Set.Cap.eq.Cap_Ite)

    Eq << Eq[-1].this.lhs.apply(Set.Inter.eq.Cap)

    Eq << Eq[-1].this.lhs.expr.apply(Set.Inter_Ite.eq.Ite_InterS)

    Eq << Eq[-1].this.lhs.expr.apply(Bool.Ite_Ite.eq.Ite__Ite)


if __name__ == '__main__':
    run()
# created on 2021-04-28
