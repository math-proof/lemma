from util import *


@apply
def apply(el, x, y):
    n, (S[1], m) = el.of(Element[Range])
    assert m > 0 and n > 0
    assert x.shape[0] >= m
    assert y.shape[0] >= m

    return Iff(Equal(x[:m], y[:m]), Equal(x[:n], y[:n]) & Equal(x[n:m], y[n:m]))

@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    m, n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(real=True, shape=(oo,))
    Eq << apply(Element(n, Range(1, m)), x, y)

    k = Symbol(domain=Eq[0].rhs)
    Eq << All[k](Eq[1].cond._subs(n, k), plausible=True)

    Eq << Eq[-1].this.expr.lhs.apply(Algebra.Eq.Is.And.Eq.split, Eq[-1].variable)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], k, n)




if __name__ == '__main__':
    run()
# created on 2023-03-26
