from util import *


def applicable(multiplicand, e):
    if e.is_rational:
        if e.is_integer:
            return True
        unrealCount = 0
        for x in multiplicand:
            if not x.is_real:
                unrealCount += 1
        return unrealCount < 2
    elif e.is_real and e > 0:
        return all(x.is_real and x > 0 for x in multiplicand)


@apply
def apply(self):
    base, e = self.of(Pow)
    multiplicand = base.of(Mul)
    assert applicable(multiplicand, e)

    pows = []

    for x in multiplicand:
        pows.append(x ** e)

    return Equal(self, Mul(*pows))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b = Symbol(real=True, nonnegative=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply((a * b) ** n)

    Eq << Eq[0].subs(n, 0)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.rhs.args[-1].apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[0] * a * b

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()
# created on 2018-08-20
