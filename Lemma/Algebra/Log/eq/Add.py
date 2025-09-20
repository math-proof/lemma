from util import *


@apply
def apply(self, pivot=None):
    args = self.of(Log[Mul])
    if pivot is None:
        adds = []
        for arg in args:
            assert arg >= 0
            adds.append(Log(arg).simplify())
        rhs = Add(*adds)
    else:
        left, right = std.array_split(args, pivot)
        left = log(Mul(*left))
        right = log(Mul(*right))
        rhs = left + right

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, c, d = Symbol(real=True, positive=True)
    Eq << apply(Log(a * b * c * d), pivot=2)

    Eq << Algebra.Eq.given.Eq.Exp.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-08-27
# updated on 2023-05-17
