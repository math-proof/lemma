from util import *


@apply
def apply(given, wrt=None):
    (x, yzw), (S[x], w) = given.of(Equal[Conditioned, Conditioned])
    
    [*args] = yzw.of(And)
    assert w in args
    args.remove(w)

    y, z = args

    if wrt is not None:
        if y.is_Equal:
            y = y.lhs
        if z.is_Equal:
            z = z.lhs

        assert wrt in {y, z}
        return Equal(x | wrt & w, x | w)
    return Equal(x | y & w, x | w)


@prove(proved=False)
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus

    x, y, z, w = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z & w, x | w), wrt=y)

    return
    Eq << Probability.eq_conditioned.then.is_nonzero.apply(Eq[0])
    Eq.xyz_nonzero, Eq.w_nonzero = Algebra.et.then.Conds.apply(Eq[-1])
    Eq << Probability.is_nonzero.then.et.apply(Eq.xyz_nonzero)
    Eq.y_nonzero, Eq.z_nonzero = Algebra.et.then.Cond.apply(Eq[-1], index=slice(1, 3))
    Eq.xy_probability = Probability.bayes.corollary.apply(Eq.y_nonzero, var=x | w)
    Eq << Probability.is_nonzero.then.is_nonzero.conditioned.apply(Eq.xyz_nonzero, wrt=w)
    Eq << Probability.is_nonzero.then.eq.bayes.apply(Pr(x | w, y, z), y, z)
    Eq << Algebra.All.then.ou.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[-3]
    Eq << Algebra.et.then.Conds.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq[0])
    Eq <<= Probability.total_probability_theorem.apply(Eq[-1].lhs, z), \
        Probability.total_probability_theorem.apply(Eq[-1].rhs.args[0], z), \
        Calculus.eq.then.eq.Integral.apply(Eq[-1], (pspace(z).symbol,))
    Eq << Eq[-3].subs(Eq.xy_probability)
    Eq << Eq[-1].subs(Eq[-2])
    Eq << Eq[-1].subs(Eq[-4])
    Eq << Algebra.ne_zero.eq.then.eq.scalar.apply(Eq[-1], Eq.y_nonzero)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-07-14
