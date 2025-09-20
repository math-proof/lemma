from util import *


@apply
def apply(self):
    (x, y), *rest = self.of(Mul[KroneckerDelta])
    rest = Mul(*rest)
    assert rest._subs(x, y) == 0 or rest._subs(y, x)
    return Equal(self, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply((f(x) - f(y)) * KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.Delta.subst)






if __name__ == '__main__':
    run()
# created on 2022-10-11
# updated on 2023-03-17
