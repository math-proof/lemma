from util import *


@apply
def apply(self):
    args = self.of(Min)
    x = []
    for arg in args:
        if arg.is_Floor:
            arg = arg.arg
        elif arg.is_Add:
            flrs, non_flrs = std.array_split(arg.args, lambda arg : arg.is_Floor)

            assert flrs
            arg = Add(*non_flrs)
            assert arg.is_integer

            for f in flrs:
                arg += f.arg
        else:
            return
        x.append(arg)

    return Equal(self, Floor(Min(*x)))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)
    n = Symbol(integer=True)

    Eq << apply(Min(n + floor(x), floor(y)))

    Eq << Eq[0].apply(Algebra.Eq.given.And.split.Floor)

    assert n + floor(x) <= n + x

    Eq <<= Algebra.Lt_Add_.Floor.One.apply(x) + n, Algebra.Lt_Add_.Floor.One.apply(y)

    Eq << Algebra.LtMin.of.Lt.Lt.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Min.eq.Add)

    Eq << Eq[-1] - 1

if __name__ == '__main__':
    run()
# created on 2020-01-25
