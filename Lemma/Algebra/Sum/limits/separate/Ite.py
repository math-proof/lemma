from util import *


@apply
def apply(self):
    function, *limits = self.of(Sum)
    assert len(limits) >= 2

    index = 0

    while True:
        index += 1
        _limits = self.limits[:index]
        _vars = [j for j, *_ in _limits]
        if all(not cond.has(*_vars) for expr, cond in function.of(Piecewise)):
            limits = _limits
            vars = _vars
            continue
        else:
            index -= 1
            break

    i_limit = self.limits[index:]
    assert not any(limit.has(*vars) for limit in i_limit)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in function.of(Piecewise)]

    return Equal(self, self.func(Piecewise(*ecs), *i_limit).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Finset
    i, j = Symbol(integer=True)
    A, B, C, D = Symbol(etype=dtype.integer)

    f, g, h = Function(real=True)

    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Element(i, A)), (g(i, j), Element(i, B)), (h(i, j), True))))

    Eq << Eq[0].this.lhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.expr.args[0].expr.apply(Finset.Sum.eq.Sum_MulBool)
    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(Finset.Sum.eq.Sum_MulBool)
    Eq << Eq[-1].this.rhs.expr.args[2].expr.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(functions.Bool[And]).apply(Bool.BoolAnd.eq.MulBoolS)

    Eq << Eq[-1].this.find(functions.Bool[And]).apply(Bool.BoolAnd.eq.MulBoolS)

    Eq << Eq[-1].this.find(functions.Bool[And]).apply(Bool.BoolAnd.eq.MulBoolS)

    Eq << Sum(Eq[-1].lhs.expr, Eq[-1].lhs.limits[0]).this.apply(Algebra.Sum.eq.Ite)

    Eq << Eq[-2].this.rhs.expr.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()

# created on 2020-03-17
