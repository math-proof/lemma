from util import *


@apply
def apply(self, pivot=-1):
    args, (x, a, b) = self.of(Integral[Mul])
    dv, u = std.array_split(args, pivot)
    u = Mul(*u)
    dv = Mul(*dv)

    v = self.func(dv, x).doit()
    du = diff(u, x)

# u * dv = d(u v) - du * v
    f = (u * v)._eval_interval(x, a, b) - self.func(du * v, *self.limits).simplify()
    return Equal(self, f, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, a, b = Symbol(real=True)
    u, v = Function(real=True)
    Eq << apply(Integral(u(x) * diff(v(x), x), (x, a, b)))

    @Function(real=True)
    def uv(x):
        return u(x) * v(x)
    Eq << diff(uv(x), x).this.expr.defun()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[0] - Eq[0].rhs.args[-1]

    Eq << Eq[-1].this.lhs.apply(Calculus.Add.eq.Integral)

    Eq << Eq[-1].subs(Eq[-3].reversed)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.lhs.args[0].defun()

    Eq << Eq[-1].this.lhs.defun()


if __name__ == '__main__':
    run()

# created on 2020-06-07
# updated on 2023-07-03
