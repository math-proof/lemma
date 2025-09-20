from util import *


@apply
def apply(eq, gt):
    if gt.is_Equal:
        eq, gt = gt, eq

    x, y = gt.of(Greater)
    x -= y
    lhs, rhs = eq.of(Equal)

    return Equal(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) > g(x), Equal(g(x) * (f(x) - g(x)), h(x) * f(x) + x))

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[0])

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)



if __name__ == '__main__':
    run()
# created on 2019-04-02
# updated on 2023-05-02
