from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    _a, _b = Si.of(Range)
    _a -= j
    _b -= j

    assert not _a._has(j) and not _b._has(j)
    a, b = Sj.of(Range)

    return Element(i, Range(_a + a, _b + b - 1)), Element(j, Range(Max(a, i - _b + 1), Min(b, i - _a + 1)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, i, j, n, m, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(d + j, n + j)), Element(j, Range(a, m)))

    Eq <<= Set.In_Ico.given.And.apply(Eq[0]), Set.In_Ico.given.And.apply(Eq[1]), Set.Ge.Le_Sub_1.of.In_Ico.apply(Eq[-1])

    Eq <<= Algebra.And.Ge.of.Ge_Max.apply(Eq[-2]), Algebra.And.Lt.of.Lt_Min.apply(Eq[-1])

    Eq << Algebra.Lt.of.Le.relax.apply(Eq[-2].reversed + n, lower=i)

    Eq << Algebra.Le_Sub_1.of.Lt.apply(Eq[-1]).reversed + d


if __name__ == '__main__':
    run()
# created on 2020-03-21
