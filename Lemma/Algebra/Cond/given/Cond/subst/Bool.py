from util import *


@apply
def apply(f_eq, *, cond=None, simplify=True, invert=False, assumptions={}):
    cond = sympify(cond)
    if invert:
        lhs, rhs = cond.invert(), S.false
    else:
        lhs, rhs = cond, S.true
    return f_eq._subs(lhs, rhs, simplify=simplify, assumptions=assumptions), cond


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Logic

    a, b = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f = Function(integer=True)
    Eq << apply(Equal(Piecewise((f(a), Element(a, A)), (f(b), True)), 0), cond=Element(a, A))

    Eq << Logic.Cond.BFnIte.given.And_BFn.apply(Eq[0], Eq[2])


if __name__ == '__main__':
    run()
# created on 2018-11-04
