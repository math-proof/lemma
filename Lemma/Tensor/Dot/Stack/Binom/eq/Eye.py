from util import *


@apply
def apply(self):
    (((i, j), j_limit, i_limit), (((S[i], S[j]), exp), S[j_limit], S[i_limit])) = self.of(Stack[Binomial] @ Stack[Binomial * (-1) ** Expr])
    S[j], S[0], n = j_limit
    S[i], S[0], S[n] = i_limit
    assert exp in (j - i, j + i)
    return Equal(self, Identity(n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Stack[j:n, i:n](Binomial(i, j)) @ Stack[j:n, i:n]((-1) ** (j - i) * Binomial(i, j)))

    Eq << Eq[0].this.lhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    k = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.split, cond=k <= i)

    Eq << Eq[-1].this.lhs().find(Min).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Mul.Binom.eq.Delta)
    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.Delta.eq.Eye)



if __name__ == '__main__':
    run()
# created on 2023-08-27
