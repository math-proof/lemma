from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    args = self.of(Min)
    return Equal(self * a, Min(*(arg * a for arg in args)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, x, y, z = Symbol(real=True, given=True)
    Eq << apply(a > 0, Min(x, y, z))

    b = Symbol(positive=True)
    Eq << Min(x * b, y * b, z * b).this.apply(Algebra.Min.eq.Mul)

    Eq << Eq[-1].subs(b, a)

    Eq << Eq[-1].this.args[1].simplify()

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-08-19
