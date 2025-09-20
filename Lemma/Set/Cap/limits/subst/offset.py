from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return Equal(self, limits_subs(Cap, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, n, d = Symbol(integer=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[n:a:b](f(n)), d)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.All_In.of.In_Cap), Eq[-1].this.lhs.apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Cap.given.All_In), Eq[-1].this.rhs.apply(Set.In_Cap.given.All_In)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.AllIn_Ico.of.AllIn_Ico.offset, d)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.AllIn_Ico.of.AllIn_Ico.offset, -d)


if __name__ == '__main__':
    run()
# created on 2021-01-28
