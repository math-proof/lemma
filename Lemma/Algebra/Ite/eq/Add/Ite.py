from util import *


@apply
def apply(self, pivot=-1):
    expr, cond = zip(*self.of(Piecewise))
    if not isinstance(pivot, (list, tuple)):
        pivot = [pivot] * len(expr)
    former, latter = zip(*([Add(*s) for s in std.array_split(expr.of(Add), pivot)] for expr, pivot in zip(expr, pivot)))
    return Equal(self, Piecewise(*zip(former, cond)) + Piecewise(*zip(latter, cond)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x) + g(y), Equal(x, y)), (f(x) + f(y), Element(y, A)), (h(x) + h(y), True)))

    Eq << Eq[0].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)




if __name__ == '__main__':
    run()
# created on 2023-05-22
# updated on 2023-06-08
