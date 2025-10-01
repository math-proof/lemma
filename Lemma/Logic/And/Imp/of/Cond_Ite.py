from util import *


@apply
def apply(self):
    from Lemma.Logic.Cond_Ite.Is.And.Imp import piecewise_to_et
    return piecewise_to_et(self)



@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, p = Symbol(real=True, shape=())
    A, B = Symbol(etype=dtype.real)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[0].this.rhs.apply(Logic.Ite__Ite.eq.Ite__IteAnd_Not)

    Eq << Logic.And.Imp.of.Cond.split.apply(Eq[-1], cond=Eq[0].find(Element))

    Eq << Logic.Imp.of.Imp_Ite.apply(Eq[-2])

    Eq.former, Eq.latter = Logic.And.Imp.of.Imp.split.apply(Eq[-1], cond=Eq[0].find(ExprCondPair[2]).cond)

    Eq << Logic.Imp.of.Imp_Ite.apply(Eq.former)

    Eq << Eq[-1].this.lhs.apply(Set.In_SDiff.given.And, simplify=None)

    Eq << Logic.Imp.And.of.Imp_And.subst.Bool.apply(Eq[-1], index=1, invert=True)

    Eq << Eq[2].this.lhs.apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq.latter.this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Logic.Imp.of.Imp_Ite.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-29
