from util import *


@apply
def apply(self):
    function, *limits, (x, a, b) = self.of(Stack)
    diff = b - a
    if not diff.is_Number:
        return self

    if limits:
        return

    assert function.shape
    array = []
    for i in range(diff):
        array.append(function._subs(x, sympify(i)))

    return Equal(self, BlockMatrix(array, shape=self.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = 4
    a = Symbol(real=True, shape=(oo, n))
    Eq << apply(Stack[i:n](a[i]))

    A = Symbol(Eq[0].lhs)
    B = Symbol(Eq[0].rhs)
    j = 0
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq.All_And = All[i:4](Equal(A[i], B[i]), plausible=True)

    Eq << Eq.All_And.this.apply(Algebra.All.Is.And.doit)

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    _i = Symbol('i', domain=Range(4))
    Eq << Eq.All_And.limits_subs(i, _i)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (_i, 0, 4))

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()
# created on 2019-10-16
from . import pop
from . import split
from . import shift
