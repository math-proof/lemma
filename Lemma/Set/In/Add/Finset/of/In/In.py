from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    S0 = S0.of(FiniteSet)
    S1 = S1.of(FiniteSet)
    S = {a + b for a in S0 for b in S1}


    return Element(x0 + x1, S)


@prove
def prove(Eq):
    from Lemma import Set, Bool, Nat

    x0, x1, a, b, c, d, e = Symbol(integer=True)
    Eq << apply(Element(x0, {a, b, c}), Element(x1, {d, e}))

    Eq << Set.Eq.ou.In.of.In_Insert.apply(Eq[0])

    Eq << Set.Eq.ou.In.of.In_Insert.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or, 1, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Bool.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Nat.Add.of.Eq.Eq)

    Eq << Eq[-1].this.args[1].apply(Nat.Add.of.Eq.Eq)

    Eq << Eq[-1].this.find(And).apply(Bool.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.args[2].apply(Nat.Add.of.Eq.Eq)

    Eq << Eq[-1].this.args[3].apply(Nat.Add.of.Eq.Eq)

    Eq << Eq[-1].this.find(And).apply(Bool.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.args[4].apply(Nat.Add.of.Eq.Eq)

    Eq << Eq[-1].this.args[5].apply(Nat.Add.of.Eq.Eq)

    Eq << Set.In_Finset.given.OrEqS.apply(Eq[2])




if __name__ == '__main__':
    run()
# created on 2018-11-18
# updated on 2023-05-20
-20
