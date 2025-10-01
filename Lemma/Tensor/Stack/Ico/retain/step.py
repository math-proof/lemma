from util import *


@apply
def apply(self, axis=0):
    expr, *limits = self.of(Stack)

    i, *ab = limits[axis]
    if len(ab) == 2:
        S[0], stop = ab
        stop, step = stop.of(Ceil[Expr / Expr])
        try:
            stop, start = stop.of(Expr - Expr)
        except:
            start = 0

        limits[axis] = i, Range(start, stop, step)
        expr = expr._subs(i, (i - start) / step)
    else:
        return
    return Equal(self, Stack(expr, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    d = Symbol(integer=True, positive=True)
    a, b, i = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Stack[i:Ceil((b - a) / d)](f(a + d * i)))

    Eq << Eq[0].this.rhs.apply(Tensor.Stack.Ico.simp)




if __name__ == '__main__':
    run()
# created on 2021-12-28
