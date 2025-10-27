from util import *


def limits_subs(Sum, self, old=None, new=None):
    expr, (i, a, b) = self.of(Sum)
    assert i.is_integer
    if old is None:
        old = i
        new = b - a - i - 1

    assert old == i
    c = new + i + 1
    # new = c - i - 1
    assert not c._has(i)
    # i = a => new = c - a - 1
    # i = b - 1 => new = c - (b - 1) - 1 = c - b
    return Sum[i:c - b: c - a](expr._subs(old, new))

@apply
def apply(self, old=None, new=None):
    return Equal(self, limits_subs(Sum, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Finset

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.Neg.Infty)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subst.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.In_Icc.Is.InAdd, c)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.Sum_MulBool)


if __name__ == '__main__':
    run()
# created on 2020-03-19
