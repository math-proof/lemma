from util import *


@apply
def apply(equal_sum, equal_union):
    (xi, (i, k)), n = equal_sum.of(Equal[Sum[Card, Tuple[0, Expr]]])
    x, S[i] = xi.of(Indexed)

    (S[xi], S[(i, 0, k)]), S[n] = equal_union.of(Equal[Cup, Range[0, Expr]])

    j = Symbol(domain=Range(k))
    complement = Range(k) - {j}

    return Equal(Cup[i:complement](x[i]) & x[j], xi.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    k, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(Sum[i:k](Card(x[i])), n), Equal(Cup[i:k](x[i]), Range(n)))

    Eq << Set.EqCard.of.Eq.apply(Eq[1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[0])

    Eq << Set.All_Eq_Empty.SDiff.of.Eq.apply(Eq[-1])

    j = Eq[2].lhs.args[0].index
    Eq << Eq[-1].limits_subs(i, j)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, i)

    Eq << Set.EqCupS.of.All_Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-27
