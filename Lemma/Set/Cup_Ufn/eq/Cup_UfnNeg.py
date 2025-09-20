from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Cup.given.Any_In), Eq[-1].this.lhs.apply(Set.Any_In.of.In_Cup)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any_UfnNeg.of.Any)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Any_UfnNeg.of.Any)


if __name__ == '__main__':
    run()
# created on 2018-10-05
