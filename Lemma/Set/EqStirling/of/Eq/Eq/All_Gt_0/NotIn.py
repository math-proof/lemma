from util import *


@apply
def apply(equal_sum, equal_union, all_is_positive, notcontains, s1=None):
    from sympy.functions.combinatorial.numbers import Stirling
    if not all_is_positive.is_ForAll:
        notcontains, all_is_positive, equal_sum, equal_union = given

    xi, (i, S[0], k) = all_is_positive.of(All[Card > 0])
    x, S[i] = xi.of(Indexed)

    sgm, n = equal_sum.of(Equal)
    S[xi], S[(i, 0, k)] = sgm.of(Sum[Card])

    union, interval_n = equal_union.of(Equal)
    S[0], S[n] = interval_n.of(Range)

    S[xi], S[(i, 0, k)] = union.of(Cup)

    j = Symbol(domain=Range(k))

    a = Symbol(shape=(k,), etype=dtype.integer, finiteset=True)

    if s1 is None:
        s1 = Symbol(Stirling.conditionset(n - 1, k, x))

    return Any[a:s1, j](Equal(x[i], Piecewise(({n - 1} | a[i], Equal(i, j)), (a[i], True))))


@prove(proved=False)
def prove(Eq):
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    k, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    Eq << apply(Equal(Sum[i:k + 1](Card(x[i])), n + 1),
                Equal(Cup[i:k + 1](x[i]), Range(n + 1)),
                All[i:k + 1](Card(x[i]) > 0),
                NotElement({n}, x[:k + 1].cup_finiteset()))
    return
    Eq << Set.Eq.Eq.then.is_empty.Stirling2.apply(Eq[0], Eq[1])

    Eq << Set.is_empty.then.Eq.Complement.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

# created on 2021-07-27
