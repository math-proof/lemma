from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cap)
    return Equal(self, Cap[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i](f(i)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Set.All_In.of.In_Cap, simplify=None), Eq[-1].this.lhs.apply(Set.All_In.of.In_Cap, simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Cap.given.All_In, simplify=None), Eq[-1].this.rhs.apply(Set.In_Cap.given.All_In, simplify=None)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.All.of.All.limits.Neg, simplify=None), Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.Neg, simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-01-23
