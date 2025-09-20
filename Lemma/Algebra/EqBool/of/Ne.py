from util import *



@apply
def apply(given):
    assert given.is_Unequal
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(real=True)
    f = Function(shape=(), real=True)

    Eq << apply(Unequal(f(x), y))

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2020-02-05
