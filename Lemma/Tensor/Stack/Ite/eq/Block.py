from util import *

def try_axis(ecs, limits, axis=0, shape=None):
    pivot = -axis - 1

    limit = limits[pivot]
    i, *ab = limit
    if len(ab) == 2:
        start, stop = ab
    elif len(ab) == 1:
        domain, = ab
        start, stop, S[1] = domain.args
    else:
        if ab:
            return
        start = 0
        stop = shape[axis]

    args = []
    for e, c in ecs:
        if c:
            limits[pivot] = (i, start, stop)
            X = Stack(e, *limits).simplify()
        else:
            _i, rows = c.of(Less)
            if _i != i:
                diff = _i - i

                if diff._has(i):
                    return

                rows -= diff

            limits[pivot] = (i, start, rows)
            X = Stack(e, *limits).simplify()

        args.append(X)
        start = rows
    return args

@apply
def apply(self, axis=None):
    [ecs, *limits] = self.of(Stack[Piecewise])

    shape = self.shape
    if axis is None:
        for axis in range(len(limits)):
            args = try_axis(ecs, limits, axis, shape)
            if args:
                break
    else:
        args = try_axis(ecs, limits, axis, shape)

    return Equal(self, BlockMatrix[axis](args))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n0, n1, n2, n3, m = Symbol(positive=True, integer=True, given=False)
    X0 = Symbol(shape=(m, n0), real=True)
    X1 = Symbol(shape=(m, n1), real=True)
    X2 = Symbol(shape=(m, n2), real=True)
    X3 = Symbol(shape=(m, n3), real=True)
    i, j = Symbol(integer=True)
    Eq << apply(Stack[j:n0 + n1 + n2 + n3, i:m](Piecewise((X0[i, j], j < n0), (X1[i, j - n0], j < n0 + n1), (X2[i, j - n0 - n1], j < n0 + n1 + n2), (X3[i, j - n0 - n1 - n2], True))))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n0 + n1 + n2 + n3))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)



if __name__ == '__main__':
    run()
# created on 2021-10-04
# updated on 2022-01-15
