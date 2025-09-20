from util import *


@apply
def apply(f_eq, *, old=None, new=None, simplify=True, assumptions={}):
    return f_eq._subs(old, new, simplify=simplify, assumptions=assumptions), Iff(old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f = Function(integer=True)
    Eq << apply(Equal(Piecewise((f(a), Element(a, A)), (f(b), True)), 0), old=Element(a, A), new=Element(b, B))

    Eq << Logic.Cond.of.Iff.Cond.subst.apply(Eq[2].reversed, Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-07-20
