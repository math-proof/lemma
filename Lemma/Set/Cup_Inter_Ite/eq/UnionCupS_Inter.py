from util import *


@apply
def apply(self):
    (piecewise, gx), limit = self.of(Cup[Intersection[Piecewise, Basic]])
    ecs = ((e & gx, c) for e, c in piecewise)

    return Equal(self, Piecewise(*ecs).as_multiple_terms(*limit.to_setlimit(), Cup))


@prove
def prove(Eq):
    from Lemma import Set
    A, C = Symbol(etype=dtype.integer)

    x = Symbol(integer=True)
    f, h, g = Function(etype=dtype.real)

    Eq << apply(Cup[x:A](Intersection(Piecewise((f(x), Element(x, C)), (h(x), True)), g(x), evaluate=False)))

    Eq << Eq[0].this.lhs.expr.apply(Set.Inter_Ite.eq.Ite_InterS)

    Eq << Eq[-1].this.lhs.apply(Set.Cup_Ite.eq.UnionCupS.double)


if __name__ == '__main__':
    run()

# created on 2018-10-04
