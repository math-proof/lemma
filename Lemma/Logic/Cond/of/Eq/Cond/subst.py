from util import *


@apply
def apply(eq, f_eq, *, reverse=False, simplify=True, assumptions={}, index=None):
    from Lemma.Algebra.All.of.All_Eq.Cond.subst import subs
    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
    return subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions, index=index)


@prove
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real[m][n])
    Eq << apply(Equal(a, 2 * c), Element(a * b, S))

    Eq << Eq[1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-02-06
# updated on 2022-04-01
