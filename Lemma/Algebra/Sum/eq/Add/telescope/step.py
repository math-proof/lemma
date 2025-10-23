from util import *


@apply
def apply(self, offset):
    (_xi, xi), limit = self.of(Sum[Expr - Expr])
    try:
        i, a, b = limit
    except:
        i, = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    assert i.is_integer
    assert _xi == xi._subs(i, i + offset)

    pos = Zeros(*xi.shape)
    neg = Zeros(*xi.shape)
    for t in range(offset):
        pos += xi._subs(i, b + offset - 1 - t)
        neg += xi._subs(i, a + t)

    return Equal(self, pos - neg, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Int, Finset

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo, k))
    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[i:n + 1](x[i + 2] - x[i]), 2)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.unshift)
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    # https://en.wikipedia.org/wiki/Telescoping_series


if __name__ == '__main__':
    run()
# created on 2020-03-24
