from util import *


@apply
def apply(self):
    expr, (k, i, n) = self.of(Sum)
    if i:
        expr = expr._subs(k, k + i)
        n -= i
    if expr.is_Pow:
        c, hk = expr.args
        assert not c._has(k)
        a, b = hk.of_simple_poly(k)
        coeff = c ** a
        λ = c ** b
    else:
        coeff = 1
        λ = 1
        for arg in expr.of(Mul):
            if not arg._has(k):
                coeff *= arg
            else:
                c, hk = arg.of(Pow)
                assert not c._has(k)
                a, b = hk.of_simple_poly(k)
                coeff *= c ** a
                λ *= c ** b

    return Equal(self, Piecewise((coeff * n, Equal(λ, 1)), (coeff * (1 - λ ** n) / (1 - λ), True)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k, n = Symbol(integer=True)
    λ = Symbol(real=True)
    Eq << apply(Sum[k:n](λ ** k))

    Eq << Logic.Cond_Ite.given.And.Imp.apply(Eq[0])

    Eq << Logic.Imp.given.ImpEq.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.EqSum.of.Ne.geometric_series, Eq[0].lhs)




if __name__ == '__main__':
    run()
# created on 2023-06-17
# updated on 2023-10-22
