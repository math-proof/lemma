from util import *


@apply
def apply(lt_zero, x=None, b=None, c=None):
    a = lt_zero.of(Expr < 0)
    assert x.is_real and not x.is_given
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, x=x, b=b, c=c)

    Eq << Logic.And.Imp.of.Cond.split.apply(Eq[0], cond=b ** 2 - 4 * a * c >= 0)

    Eq <<= Logic.Imp_And.of.ImpAnd.apply(Eq[-2]), Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Any.Lt_0.of.Lt_0.Add.ge.Zero, x=x), Eq[-1].this.rhs.apply(Algebra.Lt_0.of.Lt_0.Add.lt.Zero, x=x)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Cond, wrt=x)

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()
# created on 2022-04-02
