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

    diff = j - _a
    if b.is_Infinity and _b.is_Infinity:
        ...
    elif diff != b - _b or diff.has(i, j):
# _a <= i < _b
# _a <= i < j - diff
# _a + diff <= i + diff < j
# a <= i + diff < j
# a <= j < b
# then
# a <= i + diff < j < b
# a - diff <= i < j - diff

        diff = j - _b + 1

        diff_a = a - _a
        if diff == diff_a:
            return Sum(function, (j, i + diff, b), (i, _a, b - diff))
        elif diff == diff_a + 1:
            return Sum(function, (j, i + diff, b), (i, _a, b - diff + 1))
        else:
            raise

# _a <= i < _b
# j - diff <= i < _b
# j <= i + diff < _b + diff = b
# a <= j < b
# then:
# a <= j <= i + diff < _b + diff = b
# a <= j <= i + diff
# a <= i + diff < b
# a - diff <= i < b - diff

    return Sum(function, (j, a, i + diff + 1), (i, a - diff, _b))


@apply
def apply(self):
    return Equal(self, limits_swap(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:j + d:n, j:a:n - d](f[i] * g[i, j]))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.lhs.expr.args[-1].arg.apply(Set.In.In.transform.i_Ge_j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)




if __name__ == '__main__':
    run()

# created on 2019-11-06
# updated on 2023-05-21
from . import parallel
