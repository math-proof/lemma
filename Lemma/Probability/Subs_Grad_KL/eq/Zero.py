from util import *


@apply
def apply(self):
    (((cond_x, limits_quote), (S[cond_x], limits)), (θ_quote, S[1])), [S[θ_quote], θ] = self.of(Subs[Derivative[KL[Pr, Pr]]])
    if cond_x.is_Equal:
        x, x_var = cond_x.args
        S[θ_quote], = limits_quote
        S[θ], = limits
    else:
        (a, a_var), (s, s_var) = cond_x.of(Conditioned[Equal, Equal])
        a_scope, S[θ_quote] = limits_quote
        assert a_scope.index_contains(a)
        S[a_scope], S[θ] = limits

    return Equal(self, Zeros(*θ.shape), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability, Calculus

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    a = Symbol(random=True, integer=True)
    s = Symbol(random=True, real=True, shape=(D,))
    Eq << apply(Subs[θ_quote:θ](Derivative[θ_quote](KL(Pr[a:θ_quote](a | s), Pr[a:θ](a | s)))))

    Eq << Eq[0].this.find(KL).apply(Probability.KL.eq.Integral)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Integral)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Mul.eq.Add)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Mul)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Grad)

    Eq << Eq[-1].this.find(Integral).apply(Probability.Integral.eq.One.Conditioned)

    Eq << Eq[-1].this.find(Derivative).doit()




if __name__ == '__main__':
    run()
# created on 2023-04-20
# updated on 2023-04-26
