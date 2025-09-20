from util import *


@apply
def apply(self, d):
    assert self.is_integer
    d = sympify(d)
    assert d.is_nonzero
    assert d.is_integer
    return Equal(self, (self // d) * d + self % d)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True)
    d = Symbol(integer=True, zero=False)
    Eq << apply(n, d)

    Eq << Eq[0].this.find(Mod).apply(Algebra.Mod.eq.Sub_Mul_Div)




if __name__ == '__main__':
    run()
# created on 2023-06-04
