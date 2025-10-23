from util import *


@apply
def apply(is_positive_x, lt):
    x = is_positive_x.of(Expr > 0)
    if x.is_Pow:
        b, e = x.args
        if e > 0:
            assert x.is_finite
        elif e < 0:
            ...
        else:
            assert x.is_finite
    else :
        assert x.is_finite
    lhs, rhs = lt.of(Less)
    return Less(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a < b)

    Eq << Eq[1] - b

    Eq << Int.Lt_0.of.Gt_0.Lt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x




if __name__ == '__main__':
    run()
# created on 2019-06-26
# updated on 2023-04-16
