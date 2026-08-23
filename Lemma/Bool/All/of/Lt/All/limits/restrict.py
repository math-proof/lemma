from util import *


@apply
def apply(le, given):
    c, b = le.of(Less)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        a, S[b] = ab
        limit = (x, a, c)
    else:
        ab, = ab
        a, S[b] = ab.of(Interval)
        limit = (x, Interval(a, c, left_open=ab.left_open))

    return All(function, limit)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Set

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(c < b, All[x:Interval(a, b, right_open=True)](f(x) > 0))

    e = Symbol(positive=True)
    Eq << Set.AllIn_SDiff.of.All.apply(Eq[1], Interval(a, b - e))

    Eq << Bool.Imp.of.Cond.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, b - c)

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-12-12
