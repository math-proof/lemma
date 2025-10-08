from util import *


@apply
def apply(eq):
    (((AL, ((i, h), S[h])), (S[i], S[0], n)), ((AH, (S[i], S[h])), (S[i], S[0], S[n]))), AX = eq.of(Equal[BlockMatrix[1][Stack[Indexed[Floor[Expr / Expr] % Expr]], Stack[Indexed[Mod]]]])
    return Equal(AX[i + h * h], AX[i])


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    #|              63 - 32               |     31 - 16     | 15 - 8 | 7 - 0 |
    #|=======================================================================|
    #|                                                      |   AH   |   AL  |   higher 8 bit register and lower 8 bit register
    #|                                                      |      AX        |   16-bit register
    #|                                    |              EAX                 |   extended 32-bit register
    #|                                 RAX                                   |   64-bit register
    #| this algorithm is used in concatenated double-integer position embedding
    i = Symbol(integer=True)
    h, n = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, positive=True, even=True)
    AX = Symbol(real=True, shape=(n, d ))
    AL = Symbol(real=True, shape=(n, d / 2))
    AH = Symbol(real=True, shape=(n, d / 2))
    Eq << apply(Equal(AX, BlockMatrix[1]([Stack[i:n](AL[i // h % h]), Stack[i:n](AH[i % h])])))

    Eq << Eq[0][i]

    Eq << Eq[-1].subs(i, i + h * h)

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-3])





if __name__ == '__main__':
    run()
# created on 2022-02-18
# updated on 2022-02-19
