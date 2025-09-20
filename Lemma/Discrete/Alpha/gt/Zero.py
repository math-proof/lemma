from util import *


def alpha_step(*args):
    if len(args) == 1:
        x = args[0]
        if x.shape:
            n, = x.shape
            assert n > 0
            return Piecewise((x[0], Equal(n, 1)),
                             (x[0] + 1 / alpha(x[1:]), True))
        else:
            return x
    else:
        x, *args = args
        if x.shape:
            n, = x.shape
            assert n > 0
            return Piecewise((x[0] + 1 / alpha(*args), Equal(n, 1)),
                             (x[0] + 1 / alpha(x[1:], *args), True))
        else:
            return x + 1 / alpha(*args)


alpha = Function(eval=alpha_step, shape=())


@apply
def apply(x, n):
    return Greater(alpha(x[:n]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)

    Eq << apply(x, n)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Algebra.Cond.of.Cond.subst.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << Eq[-1].apply(Algebra.Div.gt.Zero.of.Gt_0)

    Eq << Eq[-1] + x[0]

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[-1], 0)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-09-17
