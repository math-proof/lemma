from util import *


@apply
def apply(given):
    x, self = given.of(Element)
    a, b = self.of(Interval)

    if a.is_positive:
        domain = Interval(1 / b, 1 / a, **self.kwargs_reversed)
    elif b.is_negative:
        domain = Interval(1 / a, 1 / b, **self.kwargs_reversed)
    elif a == 0 and self.left_open:
        domain = Interval(1 / b, oo, **self.kwargs_reversed)
    elif b == 0 and self.right_open:
        domain = Interval(-oo, 1 / a, **self.kwargs_reversed)

    return Element(1 / x, domain)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq <<= Algebra.LeInv.of.Ge.apply(Eq[-2]), Algebra.Gt_0.of.Ge.apply(Eq[-2])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq <<= Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[3]), Algebra.Gt.of.Gt.Le.apply(Eq[-2], Eq[3])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq <<= Algebra.GeMul.of.Gt_0.Ge.apply(Eq[-1], Eq[-3])

    Eq << Set.In.Icc.of.Ge.Le.apply(Eq[-1], Eq[4])


if __name__ == '__main__':
    run()
# created on 2020-06-21
