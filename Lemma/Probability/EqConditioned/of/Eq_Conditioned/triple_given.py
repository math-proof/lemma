from util import *


@apply
def apply(given):
    ((y, k), xy_historic), (S[y[k]], S[y[k - 1].as_boolean()]) = given.of(Equal[Conditioned[Indexed], Conditioned])

    x_historic, y_historic = xy_historic.of(And)
    if y[:k].as_boolean() != y_historic:
        x_historic, y_historic = y_historic, x_historic
    assert y[:k].as_boolean() == y_historic

    return Equal(y[k] | y_historic, y[k] | y[k - 1])


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool, Tensor

    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True, given=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(Equal(y[k] | x[:k] & y[:k], y[k] | y[k - 1]))

    Eq << Eq[0].apply(Bool.AllIn.of.All, (k, 2, oo))

    Eq << Eq[-1].this().expr.lhs.rhs.args[1].apply(Tensor.EqSliceS.Eq.of.Eq)

    Eq << Probability.Eq.of.Eq_Conditioned.single_condition_w.apply(Eq[-1], wrt=Eq[-1].lhs.rhs.args[-1].lhs)

    Eq << Eq[1].apply(Bool.All.given.All.AllNot, cond=k >= 2)

    Eq << Eq[-1].this().expr.lhs.rhs.apply(Tensor.EqSliceS.given.EqSliceS.Eq.Lt)





if __name__ == '__main__':
    run()
# created on 2021-07-15
# updated on 2023-05-20
