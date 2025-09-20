from util import *


@apply
def apply(all_historic, all_n):
    if len(all_historic.limits) == 1:
        all_historic, all_n = all_n, all_historic

    (lhs, rhs), (j, S[0], i), (_i, S[0], n_1) = all_historic.of(All[Unequal])
    if lhs._has(j):
        lhs, rhs = rhs, lhs

    (_lhs, _rhs), (S[i], S[0], S[n_1]) = all_n.of(All[Unequal])
    if _lhs._has(i):
        _lhs, _rhs = _rhs, _lhs

    n = n_1

    x = Stack[i:n + 1](lhs)
    assert x[j] == rhs

    assert x[n] == _lhs
    assert x[i] == _rhs

    return All[j:i, i:n + 1](Unequal(x[i], x[j]))


@prove
def prove(Eq):
    from Lemma import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])),
                All[i:n](Unequal(x[n], x[i])))

    Eq << Algebra.All.given.And.All.apply(Eq[-1], cond={n}, wrt=i)




if __name__ == '__main__':
    run()

# created on 2020-09-09
