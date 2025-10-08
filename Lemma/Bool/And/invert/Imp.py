from util import *


@apply
def apply(given, i=-1, j=None):
    [*args] = given.of(And)
    if i < 0:
        i += len(args)
    if j is None:
        j = i - 1

    conj = args[i]
    args[j] = Imply(conj, args[j])
    return And(*args)

@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b, x, y = Symbol(real=True)
    Eq << apply(Greater(x, y) & Greater(a, b))

    Eq << Eq[-1].this.find(Imply).apply(Bool.Imp.Is.Or_Not)

    Eq << Eq[-1].this.rhs.apply(Bool.And_Or.Is.OrAndS)


if __name__ == '__main__':
    run()
# created on 2022-09-20
