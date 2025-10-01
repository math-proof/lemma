from util import *


def rewrite(Sum, self, inverse):
    expr, *limits, (k, a, b) = self.of(Sum)
    assert b >= a
    if limits:
        back = Sum(expr, *limits)
    else:
        back = expr
#     b >= a => b >= a - 1
    front = expr._subs(k, a - 1)
    return Sum.operator(Sum[k:a - 1:b](expr, *limits), inverse(front))

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self, lambda x: -x), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    C = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.AddSumS, cond={0})





if __name__ == '__main__':
    run()

# created on 2019-11-04
# updated on 2023-03-30
