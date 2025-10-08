from util import *


@apply
def apply(self, index=0, pivot=-1):
    [*ecs] = self.of(Piecewise)
    head = ecs[:index]
    expr, cond = ecs[index]
    tail = ecs[index + 1:]

    if cond.is_And:
        eqs = cond.args

    elif cond.is_Element:
        eqs = [Element(cond.lhs, u) for u in cond.rhs.of(Intersection)]

    elif cond.is_NotElement:
        eqs = [NotElement(cond.lhs, u) for u in cond.rhs.of(Union)]

    elif cond.is_Subset:
        eqs = [Subset(cond.lhs, u) for u in cond.rhs.of(Intersection)]

    elif cond.is_Supset:
        eqs = [Supset(cond.lhs, u) for u in cond.rhs.of(Union)]

    former, latter = std.array_split(eqs, pivot)

    former = And(*former)
    latter = And(*latter)

    return Equal(self, Piecewise(*head, (Piecewise((expr, former), *tail), latter), *tail))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,))
    A, B, C = Symbol(etype=dtype.real[k])
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Element(x, C)), (f(x) * g(y), Element(x, A & B)), (h(x, y), True)), index=1)

    Eq << Eq[0].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite, index=1)





if __name__ == '__main__':
    run()

# created on 2020-02-22
# updated on 2023-06-01
