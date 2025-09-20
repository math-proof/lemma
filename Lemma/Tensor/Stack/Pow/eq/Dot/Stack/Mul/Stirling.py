from util import *


@apply
def apply(self):
    (j, i), (S[j], S[0], m), (S[i], S[0], d) = self.of(Stack[Pow])
    return Equal(self, Stack[j:d, i:d](Stirling(i, j) * Factorial(j)) @ Stack[j:m, i:d](Binomial(j, i)))

@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    m, d = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Stack[j:m, i:d](j ** i))

    x = Symbol(real=True)
    Eq << Tensor.Stack.Mul.eq.Dot.Stack.Stirling.apply(Stack[j:m, i:d](j ** i * x ** j))

    Eq << Eq[1].subs(x, 1)


if __name__ == '__main__':
    run()
# created on 2023-08-28
