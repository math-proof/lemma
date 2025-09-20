from util import *


def extract(Sum, self, order):
    lhs, rhs = self.of(KL[Pr, Pr])

    if lhs[-1].is_Tuple:
        lhs, *limits_lhs = lhs
        if lhs.is_Conditioned:
            (x, x_var), given = lhs.of(Conditioned[Equal])
        else:
            given = None
            if lhs.is_Equal:
                x, x_var = lhs.args
            else:
                x_var = {cond.of(Equal)[1] for cond in lhs.of(And)}
    else:
        x, x_var = lhs
        limits_lhs = []
        given = None

    if rhs[-1].is_Tuple:
        rhs, *limits_rhs = rhs
        if rhs.is_Conditioned:
            (x_quote, S[x_var]), S[given] = rhs.of(Conditioned[Equal])
        else:
            assert given is None
            if rhs.is_Equal:
                x_quote, S[x_var] = rhs.args
            else:
                assert x_var == {cond.of(Equal)[1] for cond in rhs.of(And)}

    else:
        x_quote, S[x_var] = rhs
        limits_rhs = []
        assert given is None

    if isinstance(x_var, set):
        if order:
            x_var = [*x_var]
            x_var.sort(key=order)
        limits = [(v,) for v in x_var]
    else:
        limits = [(x_var,)]

    return Sum(log(Pr(lhs, *limits_lhs, given=given) / Pr(rhs, *limits_rhs, given=given)) * Pr(lhs, *limits_lhs, given=given), *limits)

@apply
def apply(self, order=None):
    return Equal(self, extract(Sum, self, order))


@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(KL(Pr[θ](Equal(x, x.var)), Pr[θ_quote](Equal(x, x.var))))

    Eq << Eq[-1].this.find(KL).apply(Probability.KL.eq.Expect)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Sum)




if __name__ == '__main__':
    run()
# created on 2023-03-25
