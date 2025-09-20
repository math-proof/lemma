from util import *


@apply
def apply(self):
    assert not self.shape
    args = self.of(Add)
    args = [arg.of(Abs) for arg in args]

    return GreaterEqual(self, Abs(Add(*args)))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(abs(x) + abs(y))

    Eq << Algebra.AbsAdd.le.AddAbsS.apply(Eq[0].rhs.arg).reversed




if __name__ == '__main__':
    run()
# created on 2023-06-03
