from util import *


@apply
def apply(self, *, simplify=True):
    (ft, (t, a, b)), (x, S[1]) = self.of(Derivative[Integral])
    criteria = 1
    if b._has(x):
        if b.is_continuous_at(x):
            ...
        else:
            cond = Element(x, b.domain_defined(x, real=True)).simplify()
            criteria = Bool(cond)
        assert not a._has(x)
        dfx = Derivative[x](b)
        ft = ft._subs(t, b)
    elif a._has(x):
        assert a.is_continuous_at(x)
        assert not b._has(x)
        dfx = Derivative[x](a)
        ft = -ft._subs(t, a)

    if simplify:
        dfx = dfx.simplify()
    assert ft.is_continuous_at(t)
    return Equal(self, ft * dfx * criteria)


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    x, t, a = Symbol(real=True)
    f, h = Function(real=True, continuous=True)
    Eq << apply(Derivative[x](Integral[t:a:h(x)](f(t))))

    Eq << Eq[0].this.lhs.apply(Calculus.Grad.eq.Limit)

    epsilon = Eq[-1].lhs.variable
    Eq << Eq[-1].this.find(Add).apply(Calculus.Sub.eq.Integral)

    Eq << Calculus.All_EqLimit.IsContinuous.Icc.apply(*Eq[-1].find(Integral).args)

    Eq << Calculus.Any.Eq.Icc01.of.IsContinuous.mean_value_theorem.apply(Eq[-1], 'lamda')

    Eq.exists = Eq[-1].this.expr.apply(Calculus.Eq.Limit.Div.of.Eq, epsilon)

    Eq.Limit_f = Equal(Limit[epsilon:0](Eq.exists.expr.rhs.find(f)), f(h(x)), plausible=True)

    Eq << Eq.Limit_f.this.lhs.apply(Calculus.Limit.eq.Expr.continuity)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[0].rhs.find(Derivative).this.apply(Calculus.Grad.eq.Limit, epsilon).reversed

    Eq << Calculus.Eq_Limit.Mul.of.Eq_Limit.Eq_Limit.apply(Eq[-1], Eq.Limit_f)

    Eq << Eq.exists.this.expr.subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-05-05
# updated on 2023-06-19
