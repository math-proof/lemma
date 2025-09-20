from util import *


@apply
def apply(x, y, a, b):
    assert not x.shape and not y.shape
    return LessEqual(abs(x * y - a * b), abs(a) * abs(y - b) + abs(x - a) * abs(y))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x, y, a, b)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.MulAbsS.eq.AbsMul)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.MulAbsS.eq.AbsMul)

    Eq << Eq[-1].this.rhs.args[0].arg.expand()

    Eq << Eq[-1].this.rhs.args[0].arg.expand()

    Eq << Algebra.AddAbsS.ge.AbsAdd.apply(Eq[-1].rhs)

    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()

# created on 2019-10-01
# updated on 2023-06-03
