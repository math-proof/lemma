from util import *


@apply
def apply(ne_zero, gt):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    args = ne_zero.of(Unequal[Pr[Equal], 0])
    if args[-1].is_Tuple:
        (x, x_var), *weights = args
    else:
        x, x_var = args
        weights = []

    S[m], *_ = x.shape

    return Unequal(Pr(Equal(x[:n], x_var[:n]), *weights), 0), Unequal(Pr(Equal(x[n:m], x_var[n:m]), *weights), 0)

@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Logic

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(random=True, real=True, shape=(oo,))
    Eq << apply(Unequal(Pr(x[:m]), 0),
                m > n)

    Eq << Algebra.Iff.of.Gt.split.Eq.apply(Eq[1], *Eq[0].lhs.arg.args)

    Eq << Logic.Cond.of.Iff.Cond.subst.apply(Eq[-1], Eq[0])

    Eq << Probability.And.Ne_0.of.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-03-26
