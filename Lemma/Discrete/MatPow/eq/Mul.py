from util import *


@apply(simplify=False)
def apply(self, i=None):
    base, e = self.of(MatPow)

    from Lemma.Algebra.Add.eq.Mul import rewrite

    base, factor = rewrite(base)
    assert not factor.shape

    return Equal(self, factor ** e * MatPow(base, e), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(n, n))
    t = Symbol(real=True, zero=False)
    Eq << apply((t * A - t * B) ^ -2)

    X = Symbol(A - B, singular=False)
    Eq << X.this.definition

    Eq << Eq[-1] * t

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Discrete.EqInv.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.find(MatPow).base.definition.reversed

    Eq << Eq[-1] @ Eq[-1]



if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-01
