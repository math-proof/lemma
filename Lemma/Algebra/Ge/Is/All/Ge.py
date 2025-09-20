from util import *


@apply
def apply(ge, var=None):
    lhs, rhs = ge.of(GreaterEqual)
    assert lhs.shape
    if var is None:
        var = ge.generate_var(integer=True)
    return All[var:lhs.shape[0]](lhs[var] >= rhs[var])


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x >= y)

    Eq << Eq[0].this.rhs.apply(Tensor.All_Ge.Is.Ge.Stack)


if __name__ == '__main__':
    run()
# created on 2022-03-31
