from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr < 0)
    fa, R = contains.of(Element)
    stop, start = R.of(Interval)
    if start.is_infinite:
        start = -start
    else:
        start *= a

    if stop.is_infinite:
        stop = -stop
    else:
        stop *= a

    return Element(fa * a, Interval(start, stop, left_open=R.right_open, right_open=R.left_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t < 0, Element(x, Interval(a, b, left_open=True)))

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[1])

    Eq <<= Algebra.LtMul.of.Lt_0.Gt.apply(Eq[0], Eq[-2]), Algebra.GeMul.of.Lt_0.Le.apply(Eq[0], Eq[-1])

    Eq << Set.In.Icc.of.Lt.Ge.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-03
# updated on 2023-04-17
