from util import *


@apply
def apply(given):
    x, y = given.of(Mul > 0)
    return Or(And(x > 0, y > 0), And(x < 0, y < 0))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y > 0)

    Eq << Eq[1].this.args[1].apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.of.Lt_0.Lt_0)




if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-12
