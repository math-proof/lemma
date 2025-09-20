from util import *


@apply
def apply(le_x, le_y, lt):
    x, z = le_x.of(Expr <= Expr)
    y, S[z] = le_y.of(Expr <= Expr)
    z, S[x + y] = lt.of(Less)

    theta = Symbol(real=True)
    return Any[theta:Interval(pi / 3, pi, right_open=True)](Equal(z ** 2, x ** 2 + y ** 2 - 2 * x * y * cos(theta)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, y, z = Symbol(positive=True)
    Eq << apply(x <= z, y <= z, z < x + y)

    x = Symbol("x", x / z)
    y = Symbol("y", y / z)
    Eq << x.this.definition * z

    Eq.x_definition = Eq[-1].reversed

    Eq << y.this.definition * z

    Eq.y_definition = Eq[-1].reversed

    Eq << Eq[0] / z

    Eq.x_bound = Eq[-1].subs(Eq.x_definition)

    Eq << Eq[1] / z

    Eq.y_bound = Eq[-1].subs(Eq.y_definition)

    Eq << Eq[2] / z

    Eq << Eq[-1].reversed

    Eq << Eq[-1].subs(Eq.x_definition, Eq.y_definition)

    Eq.xy_bound = Eq[-1].this.lhs.ratsimp()

    Eq << Eq[3].this.expr.subs(Eq.x_definition, Eq.y_definition)

    Eq << Eq[-1].this.expr / (z * z)

    Eq << Eq[-1].this.expr - (Eq[-1].expr.rhs.args[-1] + 1)

    Eq.cos = Eq[-1].this.expr / (2 * x * y)

    Eq << Algebra.Le.of.Le.Le.quadratic.apply(Eq.x_bound, Eq.y_bound)

    Eq << Eq.xy_bound * Eq.xy_bound

    Eq << Eq[-1].this.lhs.expand() - 1 - 2 * x * y

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].apply(Set.In.Icc.of.Gt.Le)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], 2 * x * y)

    Eq << Set.In.Arccos.Icc.of.In.apply(Eq[-1])

    Eq << Algebra.Any.given.Any.subst.apply(Eq.cos, Eq.cos.variable, Eq[-1].lhs)

    Eq << Algebra.Any.given.Cond.apply(Eq[-1])

    # https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F




if __name__ == '__main__':
    run()
# created on 2020-12-05
# updated on 2023-05-21
