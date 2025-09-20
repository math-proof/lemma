from util import *


@apply
def apply(self):
    f, *limits = self.of(Cup)
    return Equal(self, Cup(Piecewise((f, self.limits_cond), (f.etype.emptySet, True)), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.rhs.expr.apply(Set.IteAnd.eq.InterIteS)

    Eq << Equal(Cup[x](Eq[-1].rhs.expr), Cup[x:A](f(x, y) & Eq[-1].rhs.expr.args[1]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Set.Cup_Inter_Ite.eq.UnionCupS_Inter)

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.Cup_Ite.eq.UnionCupS.double)


if __name__ == '__main__':
    run()

# created on 2018-10-04
