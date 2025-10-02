from util import *

def markov_assumptions(s, a, r, π):
    # d is the number of output actions
    # L + 1 is the length of the states
    L, = a.shape
    S[L + 1], b = s.shape
    [S[L]] = r.shape

    k = Symbol(domain=Range(1, L))
    joint = s[k + 1] & a[k] & r[k]
    return Equal(Pr[a:π](joint, given=s[:k] & a[:k] & r[:k]), Pr[a:π](joint)), \
        Unequal(Pr[a:π](s, a, r), 0)


def process_assumptions(sar_independence_assumption, ne):
    (((a, r, s1), (a_prev, r_prev, s_prev)), aπ), ((S[a], S[r], S[s1]), S[aπ]) = sar_independence_assumption.of(Equal[Pr[Conditioned[Equal & Equal & Equal, Equal & Equal & Equal]], Pr[Equal & Equal & Equal]])

    ak, ak_var = a
    rk, rk_var = r
    sk1, sk1_var = s1

    a, k = ak.of(Indexed)
    r, S[k] = rk.of(Indexed)
    s, S[k + 1] = sk1.of(Indexed)

    S[a], π = aπ

    a_var = Stack[k](ak_var).simplify()
    r_var = Stack[k](rk_var).simplify()
    s_var = Stack[k](sk1_var._subs(k, k - 1)).simplify()

    assert a_prev == (a[:k], a_var[:k]) and r_prev == (r[:k], r_var[:k]) and s_prev == (s[:k], s_var[:k])

    S[Pr[a:π](Equal(s, s_var) & Equal(a, a_var) & Equal(r, r_var))] = ne.of(Unequal[0])

    return (s, s_var), (a, a_var), (r, r_var), π


@apply
def apply(sar_independence_assumption, ne, T=None, t=None):
    (s, s_var), (a, a_var), (r, r_var), π = process_assumptions(sar_independence_assumption, ne)
    L, = r.shape

    if T is None:
        T = Symbol(integer=True, domain=Range(1, L + 1))

    if t is None:
        t = Symbol(integer=True)

    return Equal(Derivative[π](log(Pr[a:π](Equal(s[:T + 1], s_var[:T + 1]) & Equal(a[:T], a_var[:T]), Equal(r[:T], r_var[:T])))),
                 Sum[t:T](Derivative[π](log(Pr[a:π](Equal(a[t], a_var[t]), given=Equal(s[t], s_var[t]))))))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus

    b, d, L, D = Symbol(domain=Range(2, oo))
    s = Symbol(shape=(L + 1, b), real=True, random=True)
    a = Symbol(shape=(L,), domain=Range(d), random=True)
    r = Symbol(shape=(L,), real=True, random=True)
    T = Symbol(integer=True, domain=Range(1, L))
    t = Symbol(integer=True)
    π = Symbol(real=True, shape=(D,))

    Eq << apply(*markov_assumptions(s, a, r, π), T)

    Eq << Probability.And.Eq.Conditioned.of.Eq.apply(Eq[0])

    Eq << Probability.Eq.of.Ne_0.Eq.Eq.Eq.markov.decision.apply(Eq[-1], Eq[-3], Eq[-2], Eq[1], T, t)

    Eq << Eq[-1].subs(Eq[2])

    Eq << Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq[1], [slice(0, T), slice(0, T), slice(0, T + 1)])

    Eq << Algebra.EqLog.of.Ne_0.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.LogMul.eq.AddLogS)

    Eq << Eq[-1].this.find(Log[Product]).apply(Algebra.Log.eq.Sum)

    Eq << Eq[-1].this.find(Log[Mul]).apply(Algebra.LogMul.eq.AddLogS)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], [π])

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[2].this.find(Sum[~Derivative]).doit()





if __name__ == '__main__':
    run()
# created on 2023-03-22
# updated on 2023-03-28
