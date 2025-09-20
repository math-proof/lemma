from util import *


@apply
def apply(given, function):
    ((j, Aj), (i, Ai)), ((_i, Bi), (_j, Bj)) = given.of(Iff[Element & Element, Equal & Element])

    if i != _i:
        _i, Bi, _j, Bj = _j, Bj, _i, Bi
    assert _i == i
    assert _j == j

    assert not Aj._has(i)
    assert not Bi._has(j)
    return Equal(Sum[i:Ai, j:Aj](function), Sum[i:Bi](function._subs(j, Bj)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    i, j = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(etype=dtype.integer)
    g = Function(complex=True)
    h = Function(complex=True)
    Eq << apply(Iff(Element(i, A) & Element(j, f(i)), Element(j, B) & Equal(i, g(j))), h(i, j))

    Eq << Eq[0].this.find(Equal).apply(Set.Eq.Is.In)

    Eq << Logic.EqSum.of.Iff.apply(Eq[-1], h(i, j))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)




if __name__ == '__main__':
    run()

# created on 2019-09-14
# updated on 2023-08-26
