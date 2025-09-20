from util import *


@apply
def apply(lt):
    x, a = lt.of(LessEqual)
    x -= 1
    assert x.is_integer and a.is_integer
    return Less(x, a).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x + 1 <= a)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.Is.Le.strengthen)



if __name__ == '__main__':
    run()
# created on 2022-01-28
