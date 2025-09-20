from util import *


@apply
def apply(lt, step=1):
    lhs, rhs = lt.of(Less)
    assert lhs.is_integer and rhs.is_integer
    if step > 0:
        lhs += 1
    else:
        rhs -= 1
    return LessEqual(lhs, rhs).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x < a)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt.Is.Ge.strengthen)




if __name__ == '__main__':
    run()
# created on 2022-01-02
# updated on 2023-11-05
