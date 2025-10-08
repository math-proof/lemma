from util import *


@apply
def apply(given):
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[0, Expr]])
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
        x = x[offset:]

    n = n - 1
    assert n > 0
    return Equal(K(x[1:n + 1]) / H(x[1:n + 1]), H(x[:n + 1]) / K(x[:n + 1]) - x[0])


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n + 1](x[i] > 0))

    x_ = Symbol('x', real=True, positive=True, shape=(oo,))
    Eq << Discrete.Mul.eq.Add.HK.KH.apply(x_[:n + 1])

    Eq << Eq[-1].subs(x_[:n + 1], x[:n + 1])

    Eq << Bool.ImpNot.of.Or.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(Set.In_CartesianSpace.given.All.In)

    Eq << Eq[-1].this.lhs.expr.simplify()
    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-09-25
# updated on 2023-08-20
