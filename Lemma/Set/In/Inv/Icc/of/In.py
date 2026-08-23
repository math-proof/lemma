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
    from Lemma import Set, Nat, Rat

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq <<= Nat.LeInv.of.Ge.apply(Eq[-2]), Nat.Gt_0.of.Ge.apply(Eq[-2])

    Eq << Rat.Lt0Div.of.Gt_0.apply(Eq[-1])

    Eq <<= Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[3]), Nat.Gt.of.Gt.Le.apply(Eq[-2], Eq[3])

    Eq << Rat.Lt0Div.of.Gt_0.apply(Eq[-1])

    Eq <<= Nat.GeMulS.of.Ge.Gt_0.apply(Eq[-1], Eq[-3])

    Eq << Set.In_Icc.of.Le.Le.apply(Eq[-1], Eq[4])


if __name__ == '__main__':
    run()
# created on 2020-06-21
