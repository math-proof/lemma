from util import *


@apply
def apply(lamda):
    delta, (i, S[0], n), (j, S[0], S[n]) = lamda.of(Stack)

    S[i] = delta.of(KroneckerDelta[j])
    return Equal(lamda, Identity(n))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Stack[j:n, i:n](KroneckerDelta(i, j)))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2023-03-18
