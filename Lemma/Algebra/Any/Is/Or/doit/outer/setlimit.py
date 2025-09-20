from util import *


def doit(Sum, self):
    xi, * limits, (i, s) = self.args
    assert limits

    assert s.is_FiniteSet
    sgm = self.identity(xi)
    while s:
        t, *args = s.args

        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, t) for c in ab)))

        sgm = Sum.operator(sgm, Sum(xi._subs(i, t), *_limits))

        s = FiniteSet(*args)
        assert Element(t, s).is_BooleanFalse

    return sgm


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Sum[j:f(i), i:finiteset](x[i, j]))

    s = Symbol(Stack[i](Sum[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (i, finiteset))

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2019-02-22
