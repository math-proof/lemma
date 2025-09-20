from util import *


@apply
def apply(self):
    function, *limits, (x, a, b) = self.of(Stack)
    diff = b - a
    if limits:
        [(y, _a, _b)] = limits
        diff_y = _b - _a
        array = tuple(tuple(self[sympify(i), sympify(j)] for j in range(diff_y)) for i in range(diff))

    elif sh := function.shape:
        assert all(isinstance(s, (int, Integer)) for s in sh)
        diff_y, = sh
        array = tuple(tuple(self[sympify(i), sympify(j)] for j in range(diff_y)) for i in range(diff))
    else:
        array = tuple(self[sympify(i)] for i in range(diff))

    return Equal(self, Matrix(array), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic
    i = Symbol(integer=True)
    n = 4
    a = Symbol(real=True, shape=(oo,))

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
