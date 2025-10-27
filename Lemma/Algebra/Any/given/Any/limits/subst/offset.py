from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return limits_subs(Any, self, index, offset)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    n = Symbol(integer=True)
    m, d = Symbol(integer=True, given=True)
    f = Function(integer=True)
    Eq << apply(Any[n:1:m + 1](f(n) > 0), d)



    Eq << Int.AnyIn_Ico.of.AnyIn_Ico.offset.apply(Eq[-1], -d)




if __name__ == '__main__':
    run()
# created on 2019-02-14
