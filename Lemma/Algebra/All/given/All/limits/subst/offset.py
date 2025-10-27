from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return limits_subs(All, self, index, offset)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), 1)

    Eq << Int.AllIn_Ico.of.AllIn_Ico.offset.apply(Eq[1], -1)






if __name__ == '__main__':
    run()
# created on 2018-12-10
