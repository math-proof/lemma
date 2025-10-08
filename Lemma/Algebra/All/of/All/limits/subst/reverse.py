from util import *


@apply
def apply(given, old, new):
    expr, (n, a, b) = given.of(All[Tuple])
    assert n.is_integer
    assert old == n
    m = new + n + 1
    assert not m._has(n)
    # assert m == a + b
    return All[n:m - b:m - a](expr._subs(old, new))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:m + 1](f(n) > 0), n, m - n)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[0], n, m - n)

    Eq << Eq[-1].this.args[1].apply(Set.NotIn.Neg.of.NotIn)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInAdd.of.NotIn, m)

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], pivot=1, wrt=n)




if __name__ == '__main__':
    run()


# created on 2018-06-20
# updated on 2023-05-12
