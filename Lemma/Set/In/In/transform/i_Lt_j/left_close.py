from util import *


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    a_d, d_j = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = d_j - j

    assert d == a_d - a

    return And(Element(i, Range(a + d, n_d + d)), Element(j, Range(i - d + 1, n_d)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    a, i, j, n, d = Symbol(integer=True)

    Eq << apply(Element(i, Range(a + d, j + d)), Element(j, Range(a, n)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.Ico.of.In.In.i_Lt_j.i_in_j.left_close)

    Eq << Eq[-1].this.lhs.apply(Set.In.Ico.of.In.In.i_Lt_j.j_in_i.left_close)


if __name__ == '__main__':
    run()

# created on 2020-03-06
