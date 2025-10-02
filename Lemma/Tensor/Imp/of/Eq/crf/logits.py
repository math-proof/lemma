from util import *


@apply
def apply(given, G, x, s):
    t = s.definition.variable
    (x_eq, y_eq), (y, i), [S[i]] = x.definition.of(Stack[Log[Pr[Conditioned]], Tuple[Indexed]])

    return Imply(t > 0, Equal(s[t], G[y[t], y[t - 1]] + s[t - 1] + x[t, y[t]])), \
        Equal(s[t], Log(Pr(y_eq.subs(i, 0))) + Sum[i:1:t + 1](G[y[i], y[i - 1]]) + Sum[i:t + 1](x[i, y[i]]))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    # d is the number of output labels
    # oo is the length of the sequence
    d, n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, d), real=True, random=True, given=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True, given=True)
    i = Symbol(integer=True)
    t = Symbol(domain=Range(n + 1))
    joint_probability_t = Pr(x[:t + 1], y[:t + 1])
    emission_probability = Pr(x[i] | y[i])
    transition_probability = Pr(y[i] | y[i - 1])
    given = Equal(joint_probability_t, Pr(x[0] | y[0]) * Pr(y[0]) * Product[i:1:t + 1](transition_probability * emission_probability))
    y = pspace(y).symbol
    G = Symbol(Stack[y[i - 1], y[i]](log(transition_probability)))
    s = Symbol(Stack[t](log(joint_probability_t)))
    x = Symbol(Stack[y[i], i](log(emission_probability)))
    Eq.given, (Eq.s_definition, Eq.x_definition, Eq.G_definition), Eq[-2:] = apply(given, G, x, s)

    Eq << Eq.s_definition.this.rhs.subs(Eq.given)

    Eq << Eq[-1].this.rhs.apply(Algebra.LogMul.eq.AddLogS)

    Eq << Eq[-1].subs(Eq.x_definition.subs(i, 0).reversed)

    Eq << Eq[-1].this.find(Log[Product]).apply(Algebra.Log.eq.Sum)

    Eq << Eq[-1].this.find(Log[Mul]).apply(Algebra.LogMul.eq.AddLogS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Logic.Cond.of.Eq.Cond.subst.apply(Eq.x_definition.reversed, Eq[-1])

    Eq << Logic.Cond.of.Eq.Cond.subst.apply(Eq.G_definition.reversed, Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1], 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.EqSub.of.Eq.Eq, Eq[-4])

    Eq << Eq[-1].this.rhs.rhs.simplify()

    Eq << Eq[-1].this.rhs.apply(Algebra.EqAdd.Is.Eq_Sub, lhs=-1)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInAdd.of.NotIn, 1)

    Eq << Logic.ImpNot.of.Or.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.given.Gt)

    # reference: Neural Architectures for Named Entity Recognition.pdf




if __name__ == '__main__':
    run()
# created on 2020-12-17
# updated on 2025-04-20
