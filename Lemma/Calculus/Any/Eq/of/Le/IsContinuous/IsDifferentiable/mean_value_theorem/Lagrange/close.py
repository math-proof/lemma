from util import *


@apply
def apply(le, is_continuous, is_differentiable):
    a, b = le.of(LessEqual)
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_differentiable, of_continuous
    fz, (z, S[a], S[b]) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable, open=False)

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Bool, Set

    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a <= b, is_continuous(f, a, b), is_differentiable(f, a, b, open=False))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=b > a)

    Eq << Imply(b <= a, Equal(a, b), plausible=True)

    Eq << Bool.Imp.given.Or_Not.apply(Eq[-1]).reversed

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[2], Interval(a, b, left_open=True, right_open=True))

    Eq << Bool.Imp.of.Cond.apply(Eq[1] & Eq[-1], cond=b > a)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].reversed

    Eq << Eq[-1].this.rhs.apply(Calculus.Any.Eq.of.Lt.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Any.limits.relax, domain=Interval(a, b))




if __name__ == '__main__':
    run()

# created on 2020-04-29
# updated on 2023-08-26
