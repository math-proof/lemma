from util import *


def mul_to_limit(self):
    [*args] = self.of(Mul)
    for i, limit in enumerate(args):
        if limit.is_Limit:
            del args[i]
            expr, (x, x0) = limit.args

            for arg in args:
                assert not arg._has(x)

            return Limit[x:x0](Mul(expr, *args))


@apply
def apply(self):
    assert self.is_Mul
    return Equal(self, mul_to_limit(self))


@prove
def prove(Eq):
    from Lemma import Calculus

    x, x0, y = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Limit[x:x0](f(x)) * y)

    Eq << Eq[0].this.rhs.apply(Calculus.Limit.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2020-05-03
