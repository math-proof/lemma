from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)

    n, d = x.shape
    t = Symbol(domain=Range(n))
    i = Symbol(integer=True)

    joint_probability_t = Pr(x[:t + 1], y[:t + 1])
    joint_probability = Pr(x, y)
    emission_probability = Pr(x[i] | y[i])
    transition_probability = Pr(y[i] | y[i - 1])
    y = pspace(y).symbol

    G = Symbol(Stack[y[i - 1], y[i]](log(transition_probability)))

    s = Symbol(Stack[t](log(joint_probability_t)))

    x = Symbol(Stack[y[i], i](log(emission_probability)))

    x_quote = Symbol(Stack[y[t], t](Maxima[y[:t]](s[t])))

    return Imply(t > 0, Equal(x_quote[t], x[t] + ReducedMax(x_quote[t - 1] + G))), \
        Equal(Maxima[y](joint_probability), exp(ReducedMax(x_quote[n - 1])))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import markov_assumptions
    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    Eq[-4:], (*Eq[-3:], Eq.G_definition), Eq[-2:] = apply(*markov_assumptions(x, y))

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.x_quote_definition = Eq[5].apply(Tensor.EqStackS.of.Eq, (Eq[5].lhs.indices[-1],))

    y = Eq.x_quote_definition.rhs.variable.base
    Eq << Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov.apply(*Eq[:4])

    Eq << Tensor.Imp.of.Eq.crf.logits.apply(Eq[-1], Eq.G_definition.lhs.base, Eq[6].lhs.base, s)

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq.subst.rhs)

    Eq << Eq[-1].this.find(Maxima).apply(Algebra.Maxima.limits.pop.Slice)

    Eq << Eq[-1].this.find(Maxima).simplify()

    Eq << Eq[-1].this.find(Maxima).apply(Algebra.Maxima.eq.ReducedMax)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.ReducedMax)

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInAdd.of.NotIn, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.given.Gt)

    Eq << Eq[4].reversed

    Eq << Eq[-1].apply(Algebra.EqExp.of.Eq)

    Eq << Algebra.EqMaxima.of.Eq.apply(Eq[-1], (y[:t + 1],))

    Eq << Eq[-1].this.rhs.apply(Algebra.Maxima.eq.Exp)

    Eq << Algebra.EqReducedMax.of.Eq.apply(Eq.x_quote_definition)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)

    # https://arxiv.org/abs/1603.01360




if __name__ == '__main__':
    run()

# created on 2020-12-20
# updated on 2025-04-20
