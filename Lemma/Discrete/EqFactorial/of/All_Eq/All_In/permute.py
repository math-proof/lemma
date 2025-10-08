from util import *


@apply
def apply(all0, all1):

    (ref, s), (j, S[1], n_munis_1), (x, S[s]) = all0.of(All[Element])

    piecewise, (i, S[0], S[n_munis_1]) = ref.of(Stack)
    assert s.is_set
    dtype = s.etype

    (x0, condition0), (xj, conditionj), (xi, S[True]) = piecewise.of(Piecewise)
    S[i] = condition0.of(Equal[j])
    S[i] = conditionj.of(Equal[0])

    n = n_munis_1

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    equality, (S[x], S[s]) = all1.of(All)
    S[Card(x.cup_finiteset())] = equality.of(Equal[n])

    return Equal(Card(s), factorial(n) * Card(Cup[x:s]({x.cup_finiteset()})))


@prove(proved=False)
def prove(Eq):
    from Lemma import Discrete, Set, Bool

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    Eq << apply(All[j:1:n, x:S](Element(Stack[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S)),
                All[x:S](Equal(Card(x.cup_finiteset()), n)))

    Eq << Discrete.Eq.of.Eq.swap2.general.apply(Eq[0])

    Eq.permutation = Discrete.All_In.of.All_In.swapn.permutation.apply(Eq[-1])

    Eq << Eq.permutation.limits[0][1].this.definition

    Eq << Discrete.Abs.Cup.eq.Factorial.apply(n)

    Eq << Eq[-1].this.lhs.arg.limits_subs(Eq[-1].lhs.arg.variable, Eq[-2].rhs.variable)

    Eq << Eq[-2].apply(Set.EqCard.of.Eq)

    Eq <<= Eq[-2] & Eq[-1]

    F = Function(etype=dtype.integer[n])
    F.eval = lambda e: conditionset(x, Equal(x.cup_finiteset(), e), S)
    e = Symbol(etype=dtype.integer)
    Eq << Subset(F(e), S, plausible=True)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Set.All.of.Subset.All.apply(Eq[-1], Eq.permutation)

    Eq.all_x = All(Element(Eq[-1].lhs, F(e)), *Eq[-1].limits, plausible=True)

    Eq << Eq.all_x.this.expr.rhs.defun()

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    P = Eq[-1].limits[0][1]
    Eq << Set.All_CupFinset.eq.Ico.apply(P)

    Eq << Eq[-1].this.expr.apply(Set.Eq.of.Eq.permutation, x)

    Eq.equality_e = Eq[-3] & Eq[-1]


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-14
