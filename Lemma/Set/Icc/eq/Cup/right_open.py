from util import *


@apply
def apply(self, k=None):
    a, b = self.of(Interval)
    assert self.right_open and not self.left_open
    assert a.is_integer and b.is_integer
    if k is None:
        k = self.generate_var(integer=True)
    return Equal(self, Cup[k:a:b](Interval(k, k + 1, right_open=True)))


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(integer=True)
    Eq << apply(Interval(a, b, right_open=True))

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.Icc.right_open)


if __name__ == '__main__':
    run()
# created on 2021-04-29
