from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(Add)
    *_, n, S[n] = self.shape
    if i is None:
        for i, arg in enumerate(args):
            if len(arg.shape) < 2:
                break
        else:
            return

    args[i] *= Ones(*self.shape)
    return Equal(self, Add(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    B = Symbol(real=True, shape=(n,))
    Eq << apply(A + B)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], j)








if __name__ == '__main__':
    run()
# created on 2023-03-19
