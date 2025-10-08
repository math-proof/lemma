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
    return Equal(Pr(y | x), Pr(y) * Product[j](Pr(y | x[j]) * Pr(x[j]) / Pr(y)) / Pr(x))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Bool

    m, n, t = Symbol(integer=True, positive=True)
    # suppose you have a set of documents y which is labeled with some semantic tags called keywords x;
    # now that there is a large data set consisting of pairs of y and its respective set of keywords x;
    # you are then given a new document y', how to figure out the way of choosing the keywords x with optimal probability?
    x = Symbol(integer=True, shape=(n,), random=True)
    y = Symbol(integer=True, shape=(m,), random=True)
    Eq << apply(Equal(y[t] | y[:t], y[t]), Unequal(Pr(y, x), 0))

    j = Eq[-1].find(Product).variable
    Eq << Probability.Eq.Mul.Prod.Pr.Conditioned.of.Ne_0.Eq.apply(*Eq[:2])

    Eq << Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq[1], [None, j])

    Eq << Probability.Eq.Pr.Conditioned.eq.Div.Pr.Conditioned.of.Ne_0.bayes.apply(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Probability.Ne_0.of.Ne_0.delete.apply(Eq[1], 0)


if __name__ == '__main__':
    run()
# created on 2024-06-18
