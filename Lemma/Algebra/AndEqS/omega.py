from util import *


@apply
def apply(w='w'):
    cubic_root = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    if isinstance(w, str):
        w = Symbol(w, cubic_root)
    else:
        assert w.definition == cubic_root
    w_ = ~w
    return Equal(w, cubic_root), Equal(w_, ~cubic_root), Equal(w + w_, -1), Equal(w * w_, 1), Equal(w ** 2, w_), Equal(w_ ** 2, w), Equal(w ** 3, 1)


@prove
def prove(Eq):
    from Lemma import Algebra

    Eq << apply('omega')

    Eq << Algebra.EqConj.of.Eq.apply(Eq[0])

    Eq << Eq[1] + Eq[0]

    Eq << Eq[1] * Eq[0]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq <<= Eq[0] ** 2, Eq[1] ** 2

    Eq <<= Eq[-2].this.rhs.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2), Eq[-1].this.rhs.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq <<= Eq[-2].subs(Eq[1].reversed), Eq[-1].subs(Eq[0].reversed)

    Eq << Eq[4] * Eq[0].lhs

    Eq << Eq[-1].subs(Eq[3])


if __name__ == '__main__':
    run()
# created on 2018-08-18
