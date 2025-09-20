from util import *


@apply
def apply(ne_zero_prob_y_tilde_overline, y_tilde_overline_given_y, y_tilde_overline_def):
    (y_tilde_overline, y), S[y_tilde_overline] = y_tilde_overline_given_y.of(Equal[Conditioned])
    ((S[y_tilde_overline.as_boolean()], x), (y_tilde, S[x])) = y_tilde_overline_def.of(Equal[Pr[Conditioned], 1 - Pr[Conditioned]])
    S[y_tilde_overline.as_boolean()], x, S[y] = ne_zero_prob_y_tilde_overline.of(Unequal[Pr[And], 0])
    return Equal(
        Pr(x, given=y & y_tilde_overline),
        Pr(x, y) * (1 - Pr(y_tilde, given=x)) / Pr(y & y_tilde_overline)
    )


@prove
def prove(Eq):
    from Lemma import Probability

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,), random=True)
    y = Symbol(integer=True, shape=(m,), random=True)
    y_tilde = Symbol(r"\tilde{y}", integer=True, shape=(m,), random=True)
    y_tilde_overline = Symbol(r"\overline{\tilde{y}}", integer=True, shape=(m,), random=True)
    Eq << apply(
        Unequal(Pr(x, y, y_tilde_overline), 0),
        Equal(y_tilde_overline | y, y_tilde_overline),
        Equal(Pr(y_tilde_overline | x), 1 - Pr(y_tilde | x))
    )
    Eq.ne_zero_xy = Probability.Ne_0.of.Ne_0.delete.apply(Eq[0], 0)

    Eq.eq_div = Probability.Eq.Pr.Conditioned.eq.Div.Pr.Conditioned.of.Ne_0.bayes.apply(Eq[0], slice(2, None, -2))

    Eq << Probability.Ne_0.of.Ne_0.delete.apply(Eq.ne_zero_xy)

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-1], y)

    Eq << Probability.Eq.Pr.Conditioned.eq.Mul.Pr.Conditioned.of.Ne_0.bayes.apply(Eq.ne_zero_xy, y_tilde_overline, y)

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq.ne_zero_xy, Eq[1])

    Eq << Eq[-3].reversed

    Eq << Eq.eq_div.subs(*Eq[-3:], Eq[2])

    # http://myhz0606.com/article/negative_prompt



if __name__ == '__main__':
    run()
# created on 2024-06-20
# updated on 2024-06-24
