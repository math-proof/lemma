from util import *


@apply
def apply(given):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    (x, j), (S[j], S[0], n) = given.of(All[Indexed > 0])
    return Unequal(alpha(x[:n]), 0)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Logic

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] > 0))

    x_ = Symbol('x', real=True, positive=True, shape=(oo,))
    Eq << Discrete.Alpha.ne.Zero.apply(x_[:n])

    Eq << Eq[-1].subs(x_[:n], x[:n])

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(Set.In_CartesianSpace.given.All.In)

    Eq << Eq[-1].this.lhs.expr.simplify()
    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-09-22
# updated on 2023-08-20


from . import offset
