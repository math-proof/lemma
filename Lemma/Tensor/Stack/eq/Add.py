from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Stack[Add])
    rhs = []
    for f in args:
        f = self.func(f, *limits).simplify(squeeze=True)
        rhs.append(f)

    return Equal(self, Add(*rhs), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n, n), real=True)
    Eq << apply(Stack[i:n](x[j, i] + y[i, j]))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-13
