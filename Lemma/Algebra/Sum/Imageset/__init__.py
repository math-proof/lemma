from util import *


@apply
def apply(self):
    f, (m, domain) = self.of(Sum)
    n, expr, base_set = domain.image_set()

    assert expr.as_poly(n).degree() == 1
    f = f._subs(m, expr)

    return Equal(self, self.func(f, (n, base_set)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Finset

    n, a, b, m = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    h = Function(real=True)
    Eq << apply(Sum[n:imageset(n, a * n + b, h(n) > 0)](f[n]))

    Eq << Eq[0].this.lhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.lhs.limits_subs(n, m)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, b)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, b)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.absorb)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.Imageset.proportional)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.absorb)


if __name__ == '__main__':
    run()
# created on 2018-05-02
from . import proportional
