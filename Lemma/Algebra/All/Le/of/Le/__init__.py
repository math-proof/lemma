from util import *


@apply
def apply(le, var=None):
    from Lemma.Algebra.Le.given.All.Le import all_getitem
    return all_getitem(le, LessEqual, var=var)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x <= y)

    Eq << Eq[0].this.apply(Algebra.Le.Is.All.Le)




if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01

from . import monotone
