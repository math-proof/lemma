from util import *


@apply
def apply(self):
    f, *limits = self.of(Cap)
    return Equal(self, Cap(Piecewise((f, self.limits_cond), (f.etype.universalSet, True)), *((x,) for x, *_ in limits)))


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f = Function(etype=dtype.real)

    Eq << apply(Cap[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.rhs.expr.apply(Set.Ite.eq.Union)

    Eq << Equal(Cap[x](Eq[-1].rhs.expr), Cap[x:A](f(x, y) | Eq[-1].rhs.expr.args[1]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Set.Cap_Union_Ite.eq.InterCapS_Union)

    Eq << Set.EqCap.of.Eq.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.Cap_Ite.eq.InterCapS)


if __name__ == '__main__':
    run()

# created on 2021-01-27
