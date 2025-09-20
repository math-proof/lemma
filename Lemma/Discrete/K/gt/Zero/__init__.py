from util import *


@apply
def apply(x):
    from Lemma.Discrete.K.eq.Add.definition import K
    assert x.is_positive
    return Greater(K(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x[:n])

    Eq.initial0 = Eq[0].subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.lhs.defun()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.lhs.defun()

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis * x[n + 1] + Eq[0]

    Eq << Imply(Eq.hypothesis & Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.Cond.Imp.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

# created on 2020-11-06
from . import of
