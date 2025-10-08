from util import *


@apply
def apply(is_nonnegative, k=None):
    n = is_nonnegative.of(Expr >= 0)
    assert n.is_integer
    if k is None:
        k = is_nonnegative.generate_var(integer=True)
    return Equal(Cup[k:n](Interval(k, k + 1, right_open=True)), Interval(0, n, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n, k = Symbol(integer=True)
    Eq << apply(n >= 0, k)

    m = Symbol(integer=True, nonnegative=True)
    Eq << Set.Cup.eq.Icc.induct.right_open.apply(Cup[k:m](Eq[1].lhs.expr))

    Eq << Eq[-1].subs(m, n)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Bool.Cond.of.And.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2021-02-19
# updated on 2023-05-20
