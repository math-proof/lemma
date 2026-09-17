from util import *


@apply
def apply(given, wrt=None):

    (x, given), S[x] = given.of(Equal[Conditioned[And]])

    if wrt is None:
        wrt = 0

    if isinstance(wrt, int):
        wrt = given[wrt]
    elif isinstance(wrt, slice):
        wrt = And(*given[wrt])
    else:
        wrt = wrt.as_boolean()
        assert wrt in given

    return Equal(x | wrt, x)


@prove
def prove(Eq):
    from Lemma import Random, Real, Nat, Rat

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z, x))

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq.y_nonzero, Eq.z_nonzero = Random.All_NeProb_0.All_NeProb_0.of.All_Ne0ProbJoint.apply(Eq[-1])

    Eq.xy_probability = Random.All_Eq_MulProbCond.of.PSpace_Joint.apply(Eq.y_nonzero, x)

    Eq << Random.All_Eq_MulProbCond.of.PSpace_Joint.apply(Eq[2], x)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Random.All_EqIntegral_ProbJoint.of.PSpace_Joint.apply(Integral[z.bvar](Eq[-1].lhs)), \
        Random.All_EqIntegral_ProbJoint.of.PSpace_Joint.apply(Integral[z.bvar](Eq[2].lhs)), \
        Real.Integral.of.All_Eq.apply(Eq[-1], (z.bvar,))

    Eq << Eq[-3].subs(Eq.xy_probability)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[-4])

    Eq << Nat.Eq_Div.of.Eq.Ne_0.apply(Eq[-1], Eq.y_nonzero)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()

# created on 2020-12-13
# updated on 2023-05-14
