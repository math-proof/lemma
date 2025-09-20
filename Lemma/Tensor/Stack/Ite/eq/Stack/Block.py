from util import *


@apply
def apply(self):
    ecs, limit, *limits = self.of(Stack[Piecewise])
    i, *ab = limit
    if len(ab) == 2:
        a, b = ab
        n = b - a
    else:
        domain, = ab
        n = Card(domain)

    args = []
    index = 0
    for e, c in ecs:
        if c:
            X = Stack(e, (i, index, n)).simplify()
        else:
            _i, rows = c.of(Less)
            if _i != i:
                diff = _i - i
                assert not diff._has(i)
                rows -= diff
            X = Stack(e, (i, index, rows)).simplify()

        args.append(X)
        index = rows

    return Equal(self, Stack(BlockMatrix(args), *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    N, n0, n1, n2, n3, m = Symbol(positive=True, integer=True, given=False)
    X0 = Symbol(shape=(N, n0, m), real=True)
    X1 = Symbol(shape=(N, n1, m), real=True)
    X2 = Symbol(shape=(N, n2, m), real=True)
    X3 = Symbol(shape=(N, n3, m), real=True)
    i, k = Symbol(integer=True)
    Eq << apply(Stack[i:n0 + n1 + n2 + n3, k:N](Piecewise((X0[k, i], i < n0), (X1[k, i - n0], i < n0 + n1), (X2[k, i - n0 - n1], i < n0 + n1 + n2), (X3[k, i - n0 - n1 - n2], True))))

    k = Symbol(domain=Range(N))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], k)

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.Ite.eq.Block)


if __name__ == '__main__':
    run()
# created on 2021-12-30
