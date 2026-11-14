from util import *


@apply
def apply(given):
    (joint, *weights), _joint = given.of(Equal[Pr[Conditioned], Pr])
    if isinstance(_joint, tuple):
        joint, given = joint
        S[(joint, *weights)] = _joint
    else:
        assert _joint == joint
        given, = weights
        weights = []

    return tuple(Equal(Pr(cond, *weights, given=given), Pr(cond, *weights)) for cond in joint.of(And))


@prove
def prove(Eq):
    from Lemma import Random, Real

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(Pr(x & y | z), Pr(x, y)))

    Eq <<= Eq[-2].this.lhs.apply(Random.All_Eq_DivProbS), Eq[-1].this.lhs.apply(Random.All_Eq_DivProbS)

    Eq << Eq[0].this.lhs.apply(Random.All_Eq_DivProbS)

    Eq <<= Real.Integral.of.All_Eq.apply(Eq[-1], (y.bvar,)), Real.Integral.of.All_Eq.apply(Eq[-1], (x.bvar,))

    Eq <<= Eq[-2].this.rhs.apply(Random.All_EqIntegral_ProbJoint.of.PSpace_Joint), Eq[-1].this.rhs.apply(Random.All_EqIntegral_ProbJoint.of.PSpace_Joint)

    Eq <<= Eq[-2].this.find(Integral).apply(Random.All_EqIntegral_ProbJoint.of.PSpace_Joint), Eq[-1].this.find(Integral).apply(Random.All_EqIntegral_ProbJoint.of.PSpace_Joint)




if __name__ == '__main__':
    run()
# created on 2023-03-23
# updated on 2023-03-24
