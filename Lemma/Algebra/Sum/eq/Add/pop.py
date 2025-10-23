from util import *


def rewrite(Sum, self):
    expr, *limits, (k, a, b) = self.of(Sum)
    assert a <= b - 1
    if limits:
        back = Sum(expr, *limits)
    else:
        back = expr

    back = back._subs(k, b - 1)
#     b >= a => b + 1 >= a
    return Sum.operator(Sum[k:a:b - 1](expr, *limits), back)


@apply
def apply(self):
    return Equal(self, rewrite(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:n + 1](f(i) + h(i)))

    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.AddSumS, cond={n})





if __name__ == '__main__':
    run()
# created on 2019-04-26
# updated on 2023-03-30
