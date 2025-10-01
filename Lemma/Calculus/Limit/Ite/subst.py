from util import *


def subs(self, x, x0):
    [*args] = self.args

    if self.is_Piecewise:
        for i, (e, c) in enumerate(args):
            if c:
                continue
            if c._subs(x, oo):
                args[i] = (e, True)
                i += 1
                break
        else:
            return self
        return Piecewise(*args)

    hit = False
    for i, arg in enumerate(self.args):
        arg = subs(arg, x, x0)
        if arg == args[i]:
            continue
        args[i] = arg
        hit = True
    if hit:
        return self.func(*args)

    return self

@apply
def apply(self):
    expr, (x, x0) = self.of(Limit)
    assert x0 == oo
    _expr = subs(expr, x, x0)
    assert _expr != expr
    return Equal(self, Limit[x:x0](_expr))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Logic

    n = Symbol(integer=True)
    a = Symbol(integer=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Limit[n:oo](Piecewise((f(n), n > a), (g(n), True))))

    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1].reversed)

    Eq << Eq[-1].this.apply(Calculus.Eq.Is.Any_All.limit_definition)

    Eq << Eq[-1].this.find(Less).apply(Logic.BFn_Ite.given.OrAndS)

    Eq << Eq[-1].this.expr.apply(Algebra.All_Or.given.All)

    N = Eq[-1].variable
    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], N, Max(N, a))

    Eq << Eq[2].this.expr.apply(Set.AllIn_SDiff.of.All, Range(Max(N + 1, a + 1), oo))

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Add)

    Eq << Eq[-1].this.expr.apply(Algebra.All.And.of.All)

    Eq << Eq[-1].this.find(Element).apply(Set.Ge.Le_Sub_1.of.In_Ico)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Gt.of.Ge.relax)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.of.Gt_Max, 1)




if __name__ == '__main__':
    run()
# created on 2020-05-28
# updated on 2023-04-29
