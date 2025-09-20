from util import *


@apply
def apply(self, *, evaluate=False):
    n, d = self.of(Floor[Expr / Expr])

    q = 0
    m = 0
    for arg in n.of(Add):
        if arg == d:
            q += 1
            continue
        elif arg.is_Mul:
            try:
                i = arg.args.index(d)
                args = [*arg.args]
                del args[i]
                q += Mul(*args)
                continue
            except:
                ...

        m += arg

    return Equal(self, m // d + q, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, d, k = Symbol(integer=True)
    Eq << apply(Floor((x + d * k - 1 - d) / d, evaluate=False))

    Eq << Eq[0].this.lhs.apply(Algebra.Floor.eq.Mul.Div)

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.apply(Algebra.Floor.eq.Mul.Div)

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()

# created on 2018-08-10
