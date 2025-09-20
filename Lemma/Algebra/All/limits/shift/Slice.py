from util import *


@apply
def apply(self, index=0):
    from Lemma.Algebra.Sum.limits.shift.Slice import rewrite
    return rewrite(All, self, index)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, bool=True)
    Eq << apply(All[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.simplify()

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-07-02
