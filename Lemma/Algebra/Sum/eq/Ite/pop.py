from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    back = function._subs(i, b - 1)
    return Equal(self, Piecewise((Add(Sum[i:a:b - 1](function), back), a <= b - 1), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:n + 1](f(i)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.lhs.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Ico.Is.And)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << (n < 0).this.apply(Algebra.Sum.eq.Zero.of.Lt, Eq[-1].find(Sum))

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq[-1], Eq[-2].lhs)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)
    Eq << Eq[-1].this.find(GreaterEqual).reversed


if __name__ == '__main__':
    run()
# created on 2020-03-25
