from util import *


@apply
def apply(cond, exists):
    (fn, *limits_e), *limits_f = exists.of(Any[All])

    assert not cond.has(*(e for e, *_ in limits_e))
    assert not cond.has(*(e for e, *_ in limits_f))

    return Any(All(cond & fn, *limits_e), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    y, x = Symbol(real=True)
    B, A = Symbol(etype=dtype.real, given=True)
    g, h = Function(shape=(), integer=True)
    Eq << apply(h(A, B) > 0, Any[y:B](All[x:A]((g(x, y) > 0))))

    Eq << Eq[-1].this.expr.apply(Bool.All_And.given.All.All, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(Bool.Or.given.Cond, 1, simplify=None)

    Eq << ~Eq[-1]

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Bool.All.of.All_And.apply(Eq[-1], 1)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-14
