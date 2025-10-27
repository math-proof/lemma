from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(Add)
    if i is None:
        for i, arg in enumerate(args):
            if arg.is_Piecewise:
                break
        else:
            for i, arg in enumerate(args):
                if res := arg.of(Expr * Piecewise):
                    ceoff, pieces = res
                    arg = Piecewise(*((ceoff * e, c) for e, c in pieces))
                    break
            else:
                return
    else:
        arg = args[i]

    del args[i]
    a = Add(*args)
    return Equal(self, Piecewise(*((e + a, c) for e, c in arg.of(Piecewise))))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g, h = Function(real=True)
    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), True)) + h(x))

    Eq << Eq[0].this.rhs.apply(Nat.Ite.eq.SubIte, -h(x))


if __name__ == '__main__':
    run()

# created on 2018-01-22
# updated on 2023-05-22
