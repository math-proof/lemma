from util import *


@apply
def apply(given):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    (x, _j), (j, a, n) = given.of(All[Indexed > 0])

    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
    assert a < n
    assert offset >= 0
    a += offset
    n += offset
    return Unequal(alpha(x[a:n]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    b = Symbol(integer=True, nonnegative=True)
    a = Symbol(domain=Range(n))
    i = Symbol(integer=True)
    Eq << apply(All[i:a:n](x[i + b] > 0))

    Eq << Eq[0].this.apply(Algebra.All.limits.subst.offset, a)

    Eq << Tensor.Gt_0.Stack.of.All_Gt_0.apply(Eq[-1])

    y = Symbol(x[a + b:n + b])
    Eq << y[i].this.definition

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Discrete.Ne_0.Alpha.of.All_Gt_0.apply(Eq[-1])
    Eq << Eq[-1].this.lhs.arg.definition




if __name__ == '__main__':
    run()
# created on 2020-09-22
# updated on 2022-01-01
