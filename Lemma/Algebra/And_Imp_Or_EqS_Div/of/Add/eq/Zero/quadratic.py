from util import *


@apply
def apply(given, x=None):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    fx = given.of(Equal[0])

    x, a, b, c = quadratic_coefficient(fx, x=x)

    delta = b * b - 4 * a * c

    return Imply(Equal(a, 0) & Equal(b, 0), Equal(c, 0)), Imply(Equal(a, 0) & Unequal(b, 0), True if b == 0 else Equal(x, -c / b)), Imply(Unequal(a, 0), Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2))))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(a * x ** 2 + b * x + c, 0))

    Eq << Bool.And.Imp.of.Cond.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= Bool.Imp_And.of.ImpAnd.apply(Eq[-2]), Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst), Eq[-1].this.rhs.apply(Algebra.Or.Eq.of.Ne_0.Eq.quadratic, x=x, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Algebra.AndImpS_Eq.of.Add.eq.Zero.simple, x=x)

    Eq << Bool.And.Imp.of.Imp.apply(Eq[-1])

    # Eq <<= Eq[-2].this.apply(Algebra.suffice.flatten), Eq[-1].this.apply(Algebra.suffice.flatten)


if __name__ == '__main__':
    run()
# created on 2018-08-17
