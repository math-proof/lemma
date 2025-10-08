from util import *


@apply
def apply(self, index):
    (A, B), *limits = self.of(All[Equal])
    assert isinstance(index, slice)
    start = index.start
    stop = index.stop
    step = index.step
    n = A.shape[0]
    if stop < n:
        ...
    else:
        assert self.expr.bound_check(stop, *self.limits, upper=n)

    return All(Equal(A[index], B[index]), *limits)

@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n, u = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(n, n))
    i = Symbol(integer=True)
    Eq << apply(All[i:Range(n - u)](Equal(A[i], B[i])), slice(i, i + u))

    Eq << Bool.Imp.of.AllSetOf.apply(Eq[0])

    Eq <<= Eq[-1].this.lhs.apply(Set.In_Icc.Is.InAdd, u), Eq[-1].this.lhs.apply(Set.In_Union.of.In, Range(0, n))

    Eq <<= Eq[-2].this.lhs.apply(Set.In_Union.of.In, Range(0, n))

    Eq <<= Eq[-1] & Eq[-2]




if __name__ == '__main__':
    run()
# created on 2022-01-04
