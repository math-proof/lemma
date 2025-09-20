from util import *


@apply
def apply(eq, f_eq, swap=False, reverse=False, simplify=True, assumptions={}):
    from Lemma.Algebra.All.of.All_Eq.Cond.subst import subs
    if swap:
        f_eq, eq = eq, f_eq

    lhs, rhs = eq.of(Equal)
    assert f_eq.is_Equal

    if reverse:
        lhs, rhs = rhs, lhs

    return subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions)


@prove
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    a, b, c, d = Symbol(real=True, shape=(m, n))
    Eq << apply(Equal(a, 2 * c), Equal(a * b, d))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-04-12

