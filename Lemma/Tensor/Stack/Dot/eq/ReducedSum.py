from util import *


@apply
def apply(self):
    (*Q, K), (i, S[0], k) = self.of(Stack[MatMul])
    Q = MatMul(*Q)
    Q = Stack[i:k](Q).simplify()
    K = Stack[i:k](K).simplify()
    return Equal(self, ReducedSum(Q * K), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    i = Symbol(integer=True)
    n, d = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n + 1))
    Q = Symbol(shape=(n, d), real=True)
    K = Symbol(shape=(n, d), real=True)
    Eq << apply(Stack[i:k](Q[i] @ K[i]))

    i = Symbol(domain=Range(k))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.ReducedSum)






if __name__ == '__main__':
    run()
# created on 2022-03-16
