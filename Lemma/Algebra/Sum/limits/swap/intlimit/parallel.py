from util import *


def limits_swap(Sum, self):
    function, limit_i, limit_j = self.of(Sum)
    j, *_ = limit_j
    assert limit_i._has(j)

    try:
        i, _a, _b = limit_i
    except:
        i, = limit_i
        _ab = function.domain_defined(i)
        _a, _b = _ab.of(Range)

    try:
        j, a, b = limit_j
    except:
        j, = limit_j
        ab = function.domain_defined(j)
        a, b = ab.of(Range)

    _a -= j
    _b -= j
    assert not _a._has(j)
    assert not _b._has(j)

# _a + j <= i < _b + j
# _a <= i - j < _b
# a <= j < b
# then
# i - _b < j <= i - _a
# i - _b + 1 <= j < i - _a + 1
# max(a, i - _b + 1) <= j < min(b, i - _a + 1)
    _a, _b, a, b = _a + a, _b + b - 1, Max(a, i - _b + 1), Min(b, i - _a + 1)
# _a + a <= _a + j <= i < _b + j <= _b + b - 1
    return Sum(function, (j, a, b), (i, _a, _b))


@apply
def apply(self):
    return Equal(self, limits_swap(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    i, j, d, a = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:j + d:j + n, j:a:m](f[i] * g[i, j]))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.lhs.expr.args[-1].arg.apply(Set.In_Ico.In_Ico.transform.ij_parallel)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)


if __name__ == '__main__':
    run()
# created on 2020-03-22
