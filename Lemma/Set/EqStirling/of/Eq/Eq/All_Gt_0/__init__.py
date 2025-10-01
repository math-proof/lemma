from util import *


@apply
def apply(equal_sum, equal_union, all_is_positive):
    (x, i), (S[i], k) = all_is_positive.of(All[Card[Indexed] > 0, Tuple[0, Expr]])

    ((S[x], S[i]), S[(i, 0, k)]), n = equal_sum.of(Equal[Sum[Card[Indexed]]])

    ((S[x], S[i]), S[(i, 0, k)]), S[n] = equal_union.of(Equal[Cup[Indexed], Range[0, Expr]])

    j = Symbol(domain=Range(k))
    complement = Range(k) - {j}
    return Equal(Cup[i:complement](x[i]) - x[j], Cup[i:complement](x[i]))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    k, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(Sum[i:k](Card(x[i])), n), Equal(Cup[i:k](x[i]), Range(n)), All[i:k](Card(x[i]) > 0))

    Eq << Set.Eq_Empty.Stirling.of.Eq.Eq.apply(Eq[0], Eq[1])

    Eq << Set.EqSDiff.of.Inter.eq.Empty.apply(Eq[-1], reverse=True)

if __name__ == '__main__':
    run()

# created on 2021-03-28

from . import NotIn
