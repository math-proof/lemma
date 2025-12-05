from util import *


@apply
def apply(lt, is_continuous, is_differentiable):
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_differentiable, of_continuous
    a, b = lt.of(Less)
    if is_continuous.expr.is_Element:
        is_continuous, is_differentiable = is_differentiable, is_continuous

    fz, (z, S[a], S[b]) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:a:b](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Bool, Nat

    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < b, is_continuous(f, a, b), is_differentiable(f, a, b))

    @Function(real=True)
    def g(x):
        return (b - a) * f(x) - (f(b) - f(a)) * x
    Eq.g_definition = g(x).this.defun()

    Eq << Eq.g_definition.subs(x, a)

    Eq << Eq.g_definition.subs(x, b)

    Eq << Eq[-1] - Eq[-2]

    Eq.equal = Eq[-1].this.rhs.expand()

    [[x, ksi]] = Eq[1].expr.arg.limits
    ksi, dir = ksi.clear_infinitesimal()
    Eq.is_continuous = ForAll(Equal(Limit[x:ksi + dir](g(x)), g(ksi)), *Eq[1].limits, plausible=True)

    Eq << Eq.is_continuous.this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.rhs.defun()

    Eq << Eq[-1].this.expr.lhs.apply(Calculus.Limit.eq.Add)

    Eq << Eq[-1].this.expr.lhs.args[0].apply(Calculus.Limit.eq.Mul)

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Mul)

    Eq <<= Eq[1] & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Nat.Eq.UFn.given.Eq.UFn, swap=True)

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].this.expr.rhs.apply(Algebra.Mul.distribute)

    Eq.is_differentiable = ForAll(Element(Derivative[x](g(x)), Reals), *Eq[2].limits, plausible=True)

    Eq << Eq.is_differentiable.this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.lhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.expr.apply(Set.In.given.Add.In.IccAddS, f(b) - f(a))

    Eq << Set.All.And.of.All.apply(Eq[2], simplify=None)

    Eq << Eq[-1].this.find(Unequal).apply(Set.Sub.gt.Zero.of.Ioc.ne.Empty, simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.In.Mul.of.Gt_0.In)

    Eq << Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq.apply(Eq[0], Eq.is_continuous, Eq.is_differentiable, Eq.equal)

    Eq << Eq[-1].this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.lhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.expr - f(a)





if __name__ == '__main__':
    run()
# created on 2020-04-22
# updated on 2023-08-26
