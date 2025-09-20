from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return Equal(self, limits_subs(Maxima, self, index, offset), evaluate=False)


@prove(proved=False)
def prove(Eq):
    m, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Maxima[n:1:m + 1](f(n)), 1)


if __name__ == '__main__':
    run()
# created on 2021-09-08
