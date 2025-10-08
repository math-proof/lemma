from util import *


@apply
def apply(eq, ne):
    x_boolean, y_boolean = ne.of(Unequal[Pr[And], 0])

    ((x, t), S[x[:t].as_boolean()]), S[x[t]] = eq.of(Equal[Conditioned[Indexed]])

    if x_boolean != x.as_boolean():
        x_boolean, y_boolean = y_boolean, x_boolean

    y = y_boolean.lhs

    assert t > 0
    j = Symbol(integer=True)
    return Equal(Pr(y | x), Pr(y) * Product[j](Pr(x[j] | y)) / Pr(x))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Bool, Tensor

    m, n, t = Symbol(integer=True, positive=True)
    # suppose you have a set of documents y which is labeled with some semantic tags called keywords x;
    # now that there is a large data set consisting of pairs of y and its respective set of keywords x;
    # you are then given a new document y', how to figure out the way of choosing the keywords x with optimal probability?
    x = Symbol(integer=True, shape=(n,), random=True)
    y = Symbol(integer=True, shape=(m,), random=True)
    Eq << apply(Equal(y[t] | y[:t], y[t]), Unequal(Pr(y, x), 0))

    j = Eq[-1].find(Product).variable
    Eq << Probability.Eq.Pr.Conditioned.eq.Div.Pr.Conditioned.of.Ne_0.bayes.apply(Eq[1])

    Eq << Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq[1], [None, slice(0, t)])

    Eq.yt_given_y_historic = Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq[0], Eq[-1])

    Eq.yt_given_x_nonzero = Probability.Ne_0.Conditioned.of.Ne_0.apply(Eq[-1], x)

    Eq << Probability.Eq.of.Ne_0.bayes.Conditioned.apply(Eq.yt_given_x_nonzero, y[t])

    Eq << Eq[-1].this.lhs.find(And).apply(Tensor.EqStackS.of.EqStackS.Eq)

    Eq << Eq[-1].subs(Eq.yt_given_y_historic)

    Eq << Algebra.Eq_Div.of.Eq.Ne_0.apply(Eq[-1], Eq.yt_given_x_nonzero)

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (t, 1, m))

    t = Eq[-1].rhs.variable
    Eq << Eq[-1] * Eq[-1].find(Pow).base

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Prod.eq.Prod)

    Eq << Eq[-1].this.rhs.limits_subs(t, j)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Probability.Ne_0.of.Ne_0.delete.apply(Eq[1], 0)




if __name__ == '__main__':
    run()
# created on 2024-06-18
