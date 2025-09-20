from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, gt):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Pr[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Pr[Equal], 0])

    return GreaterEqual(KL(Pr(Equal(x_lhs, x_var), *weights_lhs), Pr(Equal(x_rhs, x_var), *weights_rhs)),
                        KL(Pr(Equal(x_lhs[:n], x_var[:n]), *weights_lhs), Pr(Equal(x_rhs[:n], x_var[:n]), *weights_rhs)))

@prove
def prove(Eq):
    from Lemma import Probability

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True, shape=(oo,))
    Eq << apply(Unequal(Pr[θ](x[:m]), 0),
                Unequal(Pr[θ_quote](x[:m]), 0),
                m > n)

    Eq << Probability.And.Ne_0.of.Ne_0.Gt.apply(Eq[0], Eq[2])

    Eq << Probability.And.Ne_0.of.Ne_0.Gt.apply(Eq[1], Eq[2])

    # notes: it is illegal to access x[n:m] because it is not proven to be existent due to indexOutOfBound error
    # we can only access it through a proven result that containing the expression we want
    Eq << Probability.GeKL.of.Ne_0.Ne_0.pdf.apply(Eq[-4], Eq[-2], Eq[-1].lhs.arg.lhs)

    Eq << Probability.EqPr.of.Gt.joint.apply(Eq[2], Eq[0].lhs)

    Eq << Probability.EqPr.of.Gt.joint.apply(Eq[2], Eq[1].lhs)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)




if __name__ == '__main__':
    run()
# created on 2023-03-26
