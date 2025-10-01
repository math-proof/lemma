from util import *


def rewrite(Sum, self):
    expr, *limits, (i, *ab) = self.of(Sum)
    if not ab:
        rgn = expr.domain_defined(i)
        ab = rgn.of(Range)

    a, b = ab
    assert a + 1 <= b
    if limits:
        front = Sum(expr, *limits)
    else:
        front = expr

    front = front._subs(i, a)
#     b >= a => b + 1 >= a
    return Sum.operator(Sum[i:a + 1:b](expr, *limits), front)

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:n + 1](f(i) + h(i)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={0})





if __name__ == '__main__':
    run()
# created on 2020-03-23
# updated on 2023-04-07
