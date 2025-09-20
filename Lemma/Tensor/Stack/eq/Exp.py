from util import *


@apply
def apply(self):
    x, *limits = self.of(Stack[Exp])
    return Equal(self, Exp(Stack(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(n,))
    Eq << apply(Stack[j:n](Exp(a[j])))

    _j = Symbol('j', domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], _j)




if __name__ == '__main__':
    run()
# created on 2022-01-03
