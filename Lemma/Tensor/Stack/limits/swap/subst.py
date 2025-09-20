from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.swap.subst import rewrite
    return Equal(self, rewrite(Stack, self))


@prove
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    g = Symbol(shape=(oo, oo), real=True)
    h = Symbol(shape=(oo,), real=True)
    Eq << apply(Stack[i:n, j:n](h[i] * g[i, j]))

    k = Symbol(integer=True)
    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    Eq << Eq[-1].this.lhs.limits_subs(j, k)


if __name__ == '__main__':
    run()
# created on 2023-05-25
