from util import *


@apply
def apply(self):
    args = self.of(Mul)

    limits = None
    factors = []
    for lamda in args:
        f, *_limits = lamda.of(Stack)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits

        factors.append(f)
    return Equal(self, Stack(Mul(*factors), *limits))

@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Stack[k:n](f(k)) * Stack[k:n](g(k)))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)





if __name__ == '__main__':
    run()
# created on 2021-12-16
