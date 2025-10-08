from util import *



@apply
def apply(given, function):
    et_j, et_i = given.of(Iff)
    Aj_contains_j, Ai_contains_i = et_j.of(And)
    j, Aj = Aj_contains_j.of(Element)
    i, Ai = Ai_contains_i.of(Element)

    Bi_contains_i, Bj_contains_j = et_i.of(And)
    _i, Bi = Bi_contains_i.of(Element)
    _j, Bj = Bj_contains_j.of(Element)

    if i != _i:
        _i, Bi, _j, Bj = _j, Bj, _i, Bi

    assert _i == i
    assert _j == j

    assert not Aj._has(i)
    assert not Bi._has(j)
    return Equal(Sum[i:Ai, j:Aj](function), Sum[j:Bj, i:Bi](function))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    i, j = Symbol(integer=True)

    A, B = Symbol(etype=dtype.integer)

    f, g = Function(etype=dtype.integer)
    h = Function(complex=True)

    Eq << apply(Iff(Element(i, A) & Element(j, f(i)), Element(j, B) & Element(i, g(j))), h(i, j))

    Eq << Eq[1].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)

    Eq << Bool.EqIteS.of.Iff.subst.apply(Eq[0], Eq[-1].lhs)


if __name__ == '__main__':
    run()

# created on 2019-09-13

from . import collapse
