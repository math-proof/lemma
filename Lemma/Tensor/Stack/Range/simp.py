from util import *


@apply
def apply(self, axis=0):
    expr, *limits = self.of(Stack)

    i, domain = limits[axis]
    start, stop, step = domain.of(Range)
    limits[axis] = i, 0, Ceil((stop - start) / step)
    expr = expr._subs(i, i * step + start)

    return Equal(self, Stack(expr, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    d = Symbol(integer=True, positive=True)
    a, b, i = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Stack[i:Range(a, b, d)](f(i)))

    i = Symbol(domain=Range(Ceil((b - a) / d)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2021-12-27
