from util import *


def markov_assumptions(x, y):
    # d is the number of output labels
    # n is the length of the sequence
    n, d = x.shape
    [S[n]] = y.shape

    k = Symbol(domain=Range(1, n))
    return Equal(x[k] | x[:k] & y[:k], x[k]), Equal(y[k] | y[:k], y[k] | y[k - 1]), Equal(y[k] | x[:k], y[k]), Unequal(Pr(x, y), 0)


def process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    x = x_independence_assumption.rhs.base
    y = y_independence_assumption.lhs.lhs.base
    assert y_independence_assumption.lhs.lhs == y_independence_assumption.rhs.lhs

    assert xy_nonzero_assumption.of(Unequal[0]) == Pr(x, y)

    assert xy_independence_assumption.rhs.base == y
    return x, y


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption, t=None):
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)
    n, _ = x.shape
    if t is None:
        t = Symbol(integer=True, domain=Range(n))
    i = Symbol(integer=True)
    return Equal(Pr(x[:t + 1], y[:t + 1]),
                    Pr(x[0] | y[0]) * Pr(y[0]) * Product[i:1:t + 1](Pr(y[i] | y[i - 1]) * Pr(x[i] | y[i])))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Logic, Tensor

    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    (Eq.x_independence, Eq.first_order_markov_assumption, Eq.xy_independence, Eq.xy_nonzero_assumption), Eq.factorization = apply(*markov_assumptions(x, y))

    x = Eq.x_independence.rhs.base
    y, k = Eq.first_order_markov_assumption.rhs.lhs.of(Indexed)
    Eq << Algebra.Cond.of.Cond.domain_defined.apply(Eq.x_independence)

    Eq << Probability.And.Ne_0.of.Ne_0.apply(Eq[-1])

    Eq << Probability.Ne_0.Conditioned.of.Ne_0.apply(Eq[-3], y[:k])

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-2], x[:k + 1], y[k])

    Eq << Eq[-1].this.lhs.arg.apply(Algebra.And.concat, i=2, j=0)

    Eq << Probability.Eq.of.Ne_0.bayes.Conditioned.apply(Eq[-3], x[k], y[k])

    Eq << Eq[-1].this.lhs.find(And).apply(Algebra.And.concat, i=2, j=0)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.xy_joint_probability = Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[2], x[:k])

    Eq << Eq[-1].subs(Eq.xy_joint_probability.reversed)

    Eq.recursion = Algebra.Eq_Div.of.Eq.Ne_0.apply(Eq[0], Eq[-1])

    Eq << Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq.xy_nonzero_assumption, [k, k])

    Eq << Probability.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq.x_independence)

    Eq << Probability.EqPr.of.Eq_Conditioned.Eq_Conditioned.joint.apply(Eq[-1], Eq.xy_independence)

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq[-1], Eq[0])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq << Algebra.Or.of.Cond.subst.apply(Eq[2], k, k + 1)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1])

    _, Eq.y_nonzero_assumption = Probability.And.Ne_0.of.Ne_0.apply(Eq.xy_nonzero_assumption)

    Eq <<= Eq[-1] & Eq.y_nonzero_assumption

    Eq.y_joint_y_historic = Eq[-1].this.lhs.arg.apply(Tensor.EqSliceS.Eq.of.Eq)

    Eq << Probability.Ne_0.Conditioned.of.Ne_0.apply(Eq.y_joint_y_historic, y[:k])

    Eq << Probability.Eq.of.Ne_0.bayes.Conditioned.apply(Eq[-1], Eq.x_independence.lhs.lhs)

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq.first_order_markov_assumption)

    Eq << Probability.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq.x_independence, wrt=y[:k])

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq.y_joint_y_historic, Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq << Algebra.EqProd.of.Eq.apply(Eq.recursion, (k, 1, k + 1))

    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, Eq.factorization.rhs.args[-1].variable)

    Eq << Eq[-1] * Eq[-1].lhs.args[0].base

    Eq.first = Eq.xy_joint_probability.subs(k, 1)

    Eq << Eq[-1].subs(Eq.first)

    t = Eq.factorization.rhs.args[-1].limits[0][2] - 1
    Eq << Algebra.Or.of.Cond.subst.apply(Eq[-1], k, t)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq.first

    # reference: Neural Architectures for Named Entity Recognition.pdf




if __name__ == '__main__':
    run()
# created on 2020-12-17
# updated on 2023-05-20
