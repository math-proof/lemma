from util import *



@apply
def apply(self):
    min_xy = self.of(Floor)

    if min_xy.is_Mul:
        for i, min_args in enumerate(min_xy.args):
            if min_args.is_Min:
                args = [*min_xy.args]
                del args[i]
                factor = Mul(*args)
                assert factor > 0
                return Equal(self, Min(*[Floor(arg * factor) for arg in min_args.args]))

    x = []
    for arg in min_xy.of(Min):
        x.append(Floor(arg))

    return Equal(self, Min(*x))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)
#     z = Symbol(real=True)
#     Eq << apply(Min(floor(x), floor(y), floor(z)))
    Eq << apply(floor(Min(x, y)))

    Eq << Eq[0].apply(Algebra.Eq.given.And.split.Floor)

    Eq <<= Algebra.Lt_Add_.Floor.One.apply(x), Algebra.Lt_Add_.Floor.One.apply(y)

    Eq << Algebra.LtMin.of.Lt.Lt.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Min.eq.Add)

    Eq << Eq[-1] - 1


if __name__ == '__main__':
    run()
# created on 2019-05-13
