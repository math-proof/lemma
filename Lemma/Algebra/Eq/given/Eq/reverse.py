from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal)
    return Equal(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra

    b, a = Symbol(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << Algebra.Eq.of.Eq.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-03-29
