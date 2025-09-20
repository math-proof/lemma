from util import *


def rewrite(self, i):
    lhs, rhs = self.of(Unequal)
    if i is None:
        if lhs.is_Stack:
            i = lhs.variables[-1]
        elif rhs.is_Stack:
            i = rhs.variable[-1]
        else:
            i = self.generate_var(integer=True)

    return Any[i:lhs.shape[0]](Unequal(lhs[i], rhs[i]))

@apply
def apply(self, i=None):
    return rewrite(self, i)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Unequal(Stack[k:n](f[k]), Stack[k:n](g[k])))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.Ne.of.Ne)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne.given.Any.Ne)


if __name__ == '__main__':
    run()
# created on 2023-05-01
