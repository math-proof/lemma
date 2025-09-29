from util import *


@apply
def apply(eq, el):
    fx, *limits = eq.of(Equal[Expectation, Zero])
    b, interval = el.of(Element)

    ((gx, S[fx ** 2]), *S[limits]), (S[fx], *S[limits]) = interval.of(Interval[0, 2 * Expectation[Mul] / Expectation[Expr ** 2]])
    assert interval.left_open
    assert interval.right_open

    vars = {v for v, *_ in limits}
    from sympy.tensor.indexed import index_intersect
    random_symbols = index_intersect(gx.random_symbols, fx.random_symbols)
    assert random_symbols
    assert all (v in vars for v in random_symbols)
    return Equal(Expectation(fx * (gx - b)), Expectation(fx * gx)), Variance(fx * (gx - b)) < Variance(fx * gx)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Set

    x = Symbol(real=True, random=True)
    b = Symbol(real=True)
    π, Q = Function(real=True)
    Eq << apply(Equal(Expectation(π(x)), 0), Element(b, Interval(0, 2 * Expectation(π(x) ** 2 * Q(x)) / Expectation(π(x) ** 2), left_open=True, right_open=True)))

    Eq << Eq[-1].this.lhs.apply(Probability.Var.eq.Sub.Expect)

    Eq << Eq[-1].this.find((~Pow) * Pow).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[-Symbol * Function]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Expectation[2]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Probability.Var.eq.Sub.Expect)

    Eq << Eq[-1].this.lhs.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Algebra.Lt_0.given.And.split.Mul.apply(Eq[-1])

    Eq << Algebra.Lt_0.given.Lt.apply(Eq[-1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.Cond.of.Cond.domain_defined.apply(Eq[-1])

    Eq << Algebra.Gt_0.of.Ne_0.apply(Eq[-1])

    Eq << Algebra.LtMul.of.Gt_0.Lt.apply(Eq[-1], Eq[-3])

    Eq << Eq[2].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].subs(Eq[0])



if __name__ == '__main__':
    run()
# created on 2023-04-14
# updated on 2024-03-11
