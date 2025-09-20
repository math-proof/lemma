from util import *


@apply
def apply(equality_A, equality_B, swap=False):
    a, b = equality_A.of(Equal)
    x, y = equality_B.of(Equal)

    if swap:
        if x.etype == a.type:
            a, b = a.set, b.set
        return Equal(x - a, y - b)

    if x.type == a.etype:
        x, y = x.set, y.set
    return Equal(a - x, b - y)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A, B, X, Y = Symbol(etype=dtype.integer[n])
    Eq << apply(Equal(A, B), Equal(X, Y))

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2021-08-30
