from util import *


@apply
def apply(self):
    x, *limits = self.of(Stack[Sin])
    return Equal(self, Sin(Stack(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(n,))
    Eq << apply(Stack[j:n](Sin(a[j])))

    _j = Symbol('j', domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], _j)


if __name__ == '__main__':
    run()
# created on 2023-06-08
