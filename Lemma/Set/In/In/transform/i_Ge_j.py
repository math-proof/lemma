from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    d_j, n = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = n - n_d
    assert d_j == j + d

    return And(Element(j, Range(a, i - d + 1)), Element(i, Range(a + d, n)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(d + j, n)), Element(j, Range(a, n - d)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.Range.of.In.In.i_Ge_j.i_in_j)

    Eq << Eq[-1].this.lhs.apply(Set.In.Range.of.In.In.i_Ge_j.j_in_i)




if __name__ == '__main__':
    run()

# created on 2019-11-06
# updated on 2023-05-21
