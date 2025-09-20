from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    w_sum, M = eq_sum.of(Equal)
    w_union, M_Interval = eq_union.of(Equal)

    S[0], S[M] = M_Interval.of(Range)

    wi_abs, limit = w_sum.of(Sum)
    wi, S[limit] = w_union.of(Cup)

    S[wi] = wi_abs.of(Card)

    i, = limit
    w, S[i] = wi.of(Indexed)

    S[M] = x.shape[0]

    j = Symbol(integer=True)

    k = w.shape[0]

    return Iff(Element(j, w[i]) & Element(i, Range(k)),
                      Equal(i, Sum[i](i * Bool(Element(j, w[i])))) & Element(j, Range(M)))


@prove(proved=False)
def prove(Eq):
    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    omega = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(omega[i])), M), Equal(Cup[i](omega[i]), k.domain), x=x)


if __name__ == '__main__':
    run()

# created on 2020-12-24
from . import w_quote
