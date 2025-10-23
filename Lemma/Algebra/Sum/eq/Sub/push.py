from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    back = function._subs(i, b)
#     b >= a => b + 1 >= a
    return Equal(self, Sum[i:a:b + 1](function) - back, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.eq.AddSumS, cond={n})


if __name__ == '__main__':
    run()

# created on 2019-11-07
