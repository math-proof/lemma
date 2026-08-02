from util import *


@apply
def apply(self):
    (xi, (i, S[1])), limit = self.of(Sum[Difference])
    try:
        S[i], a, b = limit
    except:
        S[i], = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    return Equal(self, xi._subs(i, b) - xi._subs(i, a), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Function(real=True)
    i, k = Symbol(integer=True)
    n = Symbol(integer=True)
    Eq << apply(Sum[k:i:n + 1](Difference[k](x(k))))

    Eq << Eq[0].this.find(Difference).doit()

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.telescope)


if __name__ == '__main__':
    run()
# created on 2023-10-22
