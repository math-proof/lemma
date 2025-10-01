from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    front = function._subs(i, a - 1)
    return Equal(self, Piecewise((Sum[i:a - 1:b](function) - front, b >= a), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:1:n](f(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.AddSumS, cond={0})

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=n >= 1)

    Eq <<= Logic.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Zero.of.Lt, Eq[-1].find(Sum))

    Eq << Eq[-2].this.find(Element).apply(Set.In_Ico.Is.And)

    Eq << Eq[-1].this.find(Less).reversed

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Gt.of.Ge.relax, lower=0)

    Eq << Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-03-25
