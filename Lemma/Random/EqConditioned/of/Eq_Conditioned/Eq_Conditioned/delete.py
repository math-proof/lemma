from util import *


@apply
def apply(eq_x_given_yz, z_given_y):
    (z, y), S[z] = z_given_y.of(Equal[Conditioned])

    (x, yz), (S[x], S[y]) = eq_x_given_yz.of(Equal[Conditioned, Conditioned])

    _y, _z = yz.of(And)
    if _y != y:
        _z, _y = _y, _z

    assert _z == z or _z == z.as_boolean()
    assert _y == y

    return Equal(x | z, x)


@prove
def prove(Eq):
    from Lemma import Random, Real, Bool, Nat, Rat

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z, x | y), Equal(z | y, z))

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq.y_nonzero, Eq.yz_nonzero = Bool.And_And.of.And.apply(Eq[-1])

    _, Eq.z_nonzero = Random.And.Ne_0.of.Ne_0.apply(Eq.yz_nonzero)

    Eq << Random.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq.yz_nonzero, x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Random.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq.y_nonzero, z)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.xy_probability = Random.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq.y_nonzero, x)

    Eq << Eq[-1].subs(Eq.xy_probability.reversed)

    Eq << Eq[-1].subs(Eq[1])

    y_ = pspace(y).symbol
    Eq << Random.Integral.ae.Pr.of.Measurable.Measurable.Probability.apply(Integral[y_](Eq[-1].lhs))

    Eq << Eq[-1].subs(Random.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq.z_nonzero, x))

    Eq << Real.EqIntegral.of.Eq.apply(Eq[-3], (y_,))

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Integral).apply(Random.Integral.ae.Pr.of.Measurable.Measurable.Probability)

    Eq << Nat.Eq_Div.of.Eq.Ne_0.apply(Eq[-1], Eq.z_nonzero)





if __name__ == '__main__':
    run()
# created on 2021-07-14
# updated on 2023-05-18
