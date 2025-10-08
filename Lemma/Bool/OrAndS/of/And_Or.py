from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(And)
    if i is None:
        for i, eq in enumerate(args):
            if eq.is_Or:
                break
        else :
            return
    else :
        eq = args[i]

    del args[i]
    this = self.func(*args)
    return Or(*((arg & this).simplify() for arg in eq.of(Or)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Bool

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << ~Eq[-1]

    Eq << Bool.And_And.of.And.apply(Eq[0])

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[-2], Eq[-3], invert=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()


# created on 2018-05-05
# updated on 2022-01-28

