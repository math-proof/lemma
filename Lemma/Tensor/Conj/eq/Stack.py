from util import *


@apply
def apply(self):
    expr, *limits = self.of(Conjugate[Stack])
    return Equal(self, Stack(~expr, *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    h = Function(complex=True)
    Eq << apply(Conjugate(Stack[i:n](h(i * S.ImaginaryUnit)), evaluate=False))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-24
