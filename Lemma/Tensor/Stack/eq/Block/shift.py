from util import *


@apply
def apply(self):
    func, *limits, (i, a, b) = self.of(Stack)
    if limits:
        func = Stack(func, *limits)
    assert i.is_integer
    front = func._subs(i, a).simplify()
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, BlockMatrix(front, Stack[i:a:b - 1](func._subs(i, i + 1))), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Int

    i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(Stack[i:n + 1](f(i)))

    i = Symbol(domain=Range(n + 1))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.apply(Int.Ite.eq.AddMulS)





if __name__ == '__main__':
    run()
# created on 2019-10-15
# updated on 2021-11-20
