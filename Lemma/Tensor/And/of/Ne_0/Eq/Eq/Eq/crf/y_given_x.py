from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)
    n, d = x.shape

    t = Symbol(domain=Range(n))
    i = Symbol(integer=True)

    joint_probability = Pr(x[:t + 1], y[:t + 1])
    emission_probability = Pr(x[i] | y[i])
    transition_probability = Pr(y[i] | y[i - 1])
    y_given_x_probability = Pr(y | x)
    y = pspace(y).symbol

    G = Symbol(Stack[y[i - 1], y[i]](log(transition_probability)))

    s = Symbol(Stack[t](log(joint_probability)))

    x = Symbol(Stack[y[i], i](log(emission_probability)))

    z = Symbol(Stack[y[t], t](Sum[y[:t]](E ** s[t])))

    x_quote = Symbol(Stack[t](log(z[t])))

    return Imply(t > 0, Equal(x_quote[t], logsumexp(x_quote[t - 1] + G) + x[t])), \
        Equal(-log(y_given_x_probability), logsumexp(x_quote[n - 1]) - s[n - 1])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic, Probability

    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import markov_assumptions
    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    Eq << apply(*markov_assumptions(x, y))

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.z_definition = Eq[5].apply(Tensor.EqStackS.of.Eq, (Eq[5].lhs.indices[-1],))

    Eq << Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov.apply(*Eq[:4])

    Eq << Tensor.Imp.of.Eq.crf.logits.apply(Eq[-1], Eq[8].lhs.base, Eq[7].lhs.base, s)

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq << Eq.z_definition.subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq.subst.rhs)

    Eq << Eq[-1].this.find(Exp).apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.pop.Slice)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.ReducedSum.eq.Dot)

    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)

    Eq << Eq[6].subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq <<= Eq.z_recursion & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq.subst.rhs)

    Eq << Eq[-1].this.find(Log).apply(Algebra.Log.eq.Add)

    Eq.z_definition_by_x_quote = Logic.EqUFnS.of.Eq.apply(Eq[6].reversed, exp)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Exp)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInAdd.of.NotIn, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.given.Gt)

    Eq << Eq[-1].this.find(log).apply(Tensor.Log.ReducedSum.eq.LogSumExp)

    Eq.xy_joint_nonzero = Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq[3], (slice(0, t + 1), slice(0, t + 1)))

    Eq << Probability.And.Ne_0.of.Ne_0.apply(Eq.xy_joint_nonzero)

    y = Eq[-1].lhs.arg.lhs.base
    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-2], y[:t + 1])

    Eq << Probability.Sum.eq.Pr.apply(Sum[pspace(y[:t + 1]).symbol](Eq[-1].lhs))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebra.Or.Log.of.Eq)

    Eq << Logic.And_And.of.And.apply(Eq[-1] & Eq.xy_joint_nonzero)

    Eq << Eq[-1].this.rhs.apply(Algebra.Log.eq.Add)

    Eq << Logic.EqUFnS.of.Eq.apply(Eq[4].reversed, exp)

    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])

    Eq << Eq.z_definition.apply(Algebra.EqReducedSum.of.Eq)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq.y_given_x_log.subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)

    Eq << Eq[10].this.rhs.args[1].defun().reversed

    Eq << Eq[-1] + Eq[-2]

    # reference: Neural Architectures for Named Entity Recognition.pdf
    # https://spaces.ac.cn/archives/5542




if __name__ == '__main__':
    run()
# created on 2018-12-21
# updated on 2025-04-20
