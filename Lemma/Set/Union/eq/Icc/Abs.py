from util import *


@apply
def apply(self):
    int0, int1 = self.of(Union)
    assert int1.left_open == int1.right_open == int0.left_open == int0.right_open
    a, S[-a] = int0.of(Interval)
    S[-a], S[a] = int1.of(Interval)

    if int1.left_open:
        func = Interval.open
    else:
        func = Interval
    return Equal(self, func(-abs(a), abs(a)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(Interval.open(x, -x) | Interval.open(-x, x))

    Eq << Eq[0].this.lhs.apply(Set.Union.eq.Icc)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.eq.Max)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.eq.Max)

    Eq << Eq[-1].this.find(-~Max).apply(Algebra.Max.eq.Mul.Min)




if __name__ == '__main__':
    run()
# created on 2023-06-18
