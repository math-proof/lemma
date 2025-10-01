from util import *


def absorb(Sum, self):
    (fx, (k, a, b)), fi = self.of(Sum.operator[Sum[Tuple], Basic])
    assert k.is_integer
    assert fx._subs(k, b) == fi
    return Sum[k:a:b + 1](fx)


@apply
def apply(self):
    return Equal(self, absorb(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra
    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(n + 1))
    f = Function(integer=True)
    Eq << apply(Add(Sum[k:i:n](f(k)), f(n)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={n})


if __name__ == '__main__':
    run()
# created on 2018-08-08
