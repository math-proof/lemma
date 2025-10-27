from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.Sum.limits.subst.Neg import limits_subs
    return Equal(self, limits_subs(Cup, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.Cup_Ite)

    Eq << Eq[-1].this.rhs.apply(Set.Cup_UnaryFn.eq.Cup_UnaryFnNeg)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.rhs.apply(Set.CupIn_Ico.eq.Cup_UnaryFnAdd, -c)


if __name__ == '__main__':
    run()
# created on 2018-10-07
