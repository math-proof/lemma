from util import *


@apply
def apply(lt, gt, quadratic=None):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    x, m = gt.of(Greater)
    S[x], M = lt.of(Less)
    x, a, b, c = quadratic_coefficient(quadratic, x)

    assert a > 0
    return Less(quadratic, Max(a * m * m + b * m + c, a * M * M + b * M + c))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, m, M, b, c = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x < M, x > m, quadratic=a * x * x + b * x + c)

    x = Symbol(x + b / (2 * a))
    Eq.x_definition = x.this.definition

    Eq << Eq.x_definition - Eq.x_definition.rhs.args[1]

    Eq.x_original_definition = Eq[-1].reversed

    Eq << Eq[0].subs(Eq.x_original_definition)

    Eq << Eq[-1] + b / (2 * a)

    Eq << Eq[1].subs(Eq.x_original_definition)

    Eq << Eq[-1] + b / (2 * a)

    Eq << Algebra.LtSquare.of.Lt.Gt.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].subs(Eq.x_definition)

    Eq << Eq[-1] * a

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] - b * b / (4 * a) + c

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Max)


if __name__ == '__main__':
    run()
# created on 2019-12-19
