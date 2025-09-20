from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption, eq_s, eq_x, eq_G):
    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)
    y = pspace(y).symbol
    x = pspace(x).symbol
    n, d = x.shape
    (s, t), (x_t1, y_t1) = eq_s.of(Equal[Indexed, Log[Pr[And]]])
    (G, S[y[t]], S[y[t - 1]]), _ = eq_G.of(Equal[Indexed, Log[Pr[Conditioned]]])
    return Equal(s[t], G[y[t], y[t - 1]] + s[t - 1] + x[t, y[t]])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Logic

    d, n = Symbol(domain=Range(2, oo))
    X = Symbol("x", shape=(n, d), real=True, random=True)
    Y = Symbol("y", shape=(n,), domain=Range(d), random=True)
    from Lemma.Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov import markov_assumptions
    t = Symbol(integer=True)
    y = pspace(Y).symbol
    s = Symbol(shape=(n,), real=True)
    x = Symbol(shape=(n, d), real=True)
    G = Symbol(shape=(d, d), real=True)
    (*Eq[-4:], Eq.eq_s, Eq.eq_x, Eq.eq_G), Eq[-1] = apply(*markov_assumptions(X, Y),
                                                          Equal(s[t], log(Pr(X[:t + 1], Y[:t + 1]))),
                                                          Equal(x[t, y[t]], log(Pr(X[t] | Y[t]))),
                                                          Equal(G[y[t], y[t - 1]], log(Pr(Y[t] | Y[t - 1]))))

    Eq << Tensor.Eq.of.Ne_0.Eq.Eq.Eq.crf.markov.apply(*Eq[:4], t=t)

    Eq << Eq.eq_s.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Log.eq.Add)

    Eq << Eq[-1].subs(Eq.eq_x.subs(t, 0).reversed)

    Eq << Eq[-1].this.find(Log[Product]).apply(Algebra.Log.eq.Sum)

    Eq << Eq[-1].this.find(Log[Mul]).apply(Algebra.Log.eq.Add)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    i = Symbol(integer=True)
    Eq << Logic.Cond.of.Eq.Cond.subst.apply(Eq.eq_x.subs(t, i).reversed, Eq[-1])

    Eq << Logic.Cond.of.Eq.Cond.subst.apply(Eq.eq_G.subs(t, i).reversed, Eq[-1])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1] - Eq[-2]

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1] - Eq[-1].lhs.args[1]





if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2023-05-20
