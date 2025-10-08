from util import *


@apply
def apply(all_le):
    (lhs, rhs), *limits = all_le.of(All[Greater])
    lhs = Stack(lhs, *limits).simplify()
    rhs = Stack(rhs, *limits).simplify()
    return lhs > rhs


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Tensor

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] > y[i]))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Tensor.GtStack.of.All_Gt)

    Eq << Eq[-1].this.rhs.apply(Tensor.All_Gt.given.Gt.Stack)


if __name__ == '__main__':
    run()
# created on 2022-03-31
