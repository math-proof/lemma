from util import *


@apply
def apply(eq, cond):
    from Lemma.Algebra.Gt.of.Eq.Gt import trans
    return trans(GreaterEqual, eq, cond)


@prove
def prove(Eq):
    a, x, b = Symbol(real=True)
    Eq << apply(Equal(a, x), x >= b)

    Eq << Eq[2].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-11-12

from . import subst
