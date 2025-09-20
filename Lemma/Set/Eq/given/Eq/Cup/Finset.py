from util import *


def of_cup_finiteset(self):
    ak, (k, b) = self.of(Cup[FiniteSet, Tuple[0, Expr]])
    return Stack[k:b](ak).simplify()


@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    a = of_cup_finiteset(lhs)
    b = of_cup_finiteset(rhs)
    k = lhs.variable
    return Equal(a[k], b[k])


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True, shape=(n,))

    Eq << apply(Equal(a.cup_finiteset(), b.cup_finiteset()))

    i = Eq[0].lhs.variable

    Eq << Set.Eq.Cup.Finset.of.Eq.apply(Eq[-1], (i, 0, n), simplify=None)


if __name__ == '__main__':
    run()

# created on 2021-03-29
