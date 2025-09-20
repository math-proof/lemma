from util import *


@apply
def apply(self):
    b, e = self.of(Log[Pow])
    assert b > 0
    return Equal(self, e * log(b), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    b = Symbol(real=True, positive=True)
    e = Symbol(real=True)
    Eq << apply(Log(b ** e))

    Eq << Greater(b, 0, plausible=True)

    Eq << Algebra.EqLog.of.Gt_0.apply(Eq[-1], e)


if __name__ == '__main__':
    run()
# created on 2023-04-16
