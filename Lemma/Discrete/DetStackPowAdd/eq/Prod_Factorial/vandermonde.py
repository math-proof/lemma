from util import *


@apply
def apply(self):
    (delta, i), (j, S[0], n), (S[i], S[0], S[n]) = self.of(Det[Stack[Pow]])
    delta -= j
    assert not delta._has(j)

    return Equal(self, Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    n = Symbol(domain=Range(2, oo), given=False)
    i, j = Symbol(integer=True)
    delta = Symbol(real=True)
    Eq << apply(Det(Stack[j:n, i:n]((j + delta) ** i)))

    Eq << Discrete.Prod.eq.Factorial.apply(Product[j:i](i - j))

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, 0, n))

    a = Symbol(Stack[j:n](j + delta))
    Eq << a[j].this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Stack).simplify()
    Eq << Eq[-1].this.lhs.apply(Discrete.Det.Stack.eq.Prod.vandermonde)

    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition




if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2023-03-18
