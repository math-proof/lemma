from util import *


@apply
def apply(eq1, eq2, f_eq, reverse=False):
    if not eq1.is_Equal:
        f_eq, eq1 = eq1, f_eq

    old, new = eq1.of(Equal)
    if reverse:
        old, new = new, old
    f_eq = f_eq._subs(old, new)
    old, new = eq2.of(Equal)

    if reverse:
        old, new = new, old
    f_eq = f_eq._subs(old, new)
    return f_eq


@prove
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    a, b, c, d = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real[m][n])
    Eq << apply(Equal(a, 2 * c), Equal(b, 2 * d), Element(a * b, S))

    Eq << Eq[2].subs(Eq[0])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-09-11
