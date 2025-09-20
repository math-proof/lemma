from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return Equal(self, limits_subs(Stack, self, index, offset, simplify=False), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    a, b, i, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Stack[i:a:b](f(i)), d)

    i = Symbol(domain=Range(b - a))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2021-12-29
