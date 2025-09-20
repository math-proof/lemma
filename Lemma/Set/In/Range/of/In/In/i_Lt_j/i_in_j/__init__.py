from util import *


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
    a -= 1
    assert d == a_d - a

    return Element(i, Range(a + d, n_d - 1 + d)), Element(j, Range(i - d + 1, n_d))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(a + d, j + d)), Element(j, Range(a + 1, n)))

    Eq << Set.InSub.of.In_Icc.apply(Eq[0], d)

    Eq << Set.In.given.In.Sub.apply(Eq[2], d)

    Eq <<= Set.In_Range.given.And.apply(Eq[3]), Set.In_Range.given.And.apply(Eq[-1])

    Eq <<= Set.And.of.In_Range.apply(Eq[4]), Set.And.of.In_Range.apply(Eq[1])

    Eq << Eq[-2].reversed

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[7])

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[-4], Eq[-1])

    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[6])


if __name__ == '__main__':
    run()

# created on 2021-01-29


from . import left_close
