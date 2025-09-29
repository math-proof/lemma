from util import *


def extract(recurrence):
    lhs, rhs = recurrence.args
    t, *_ = lhs.indices
    m = lhs.base

    p = rhs.as_poly(m[t - 1])
    if p is None or p.degree() != 1:
        return
    beta = p.coeff_monomial(m[t - 1])
    beta_gt = p.coeff_monomial(1)

    gt = beta_gt / (1 - beta)
    gt = gt.ratsimp()

    g = gt.base
    return m, g, beta, t


@apply
def apply(initial_condition, recurrence, k=None):
    m, g, β, t = extract(recurrence)
    S[m[0]], S[0] = initial_condition.of(Equal)

    if k is None:
        k = recurrence.generate_var(integer=True, var='k')

    assert β.is_nonzero
    return Equal(m[k], β ** k * (1 - β) * Sum[t:1:k + 1](β ** (-t) * g[t]))


@prove
def prove(Eq):
    from Lemma import Algebra

    m, g = Symbol(shape=(oo,), real=True)
    t, k = Symbol(integer=True)
    beta = Symbol(real=True, nonzero=True)
    Eq << apply(Equal(m[0], 0), Equal(m[t], beta * m[t - 1] + (1 - beta) * g[t]), k=k)

    Eq << Eq[1] / beta ** t

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq[-1].this.rhs.collect(g[t])

    k = Eq[2].lhs.indices[0]
    Eq << Eq[-1].apply(Algebra.EqSumS.of.Eq, (t, 1, k + 1))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1] - Eq[-1].rhs.args[1]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] * beta ** k

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.find(Add).apply(Algebra.AddMulS.eq.Mul_Add)

    # https://arxiv.org/abs/1412.6980




if __name__ == '__main__':
    run()

# created on 2020-12-22
# updated on 2023-10-22
