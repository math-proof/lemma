from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.absorb import rewrite
    return Equal(self, rewrite(Integral, self))


@prove(proved=False)
def prove(Eq):
    x, a = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:0:oo](f(x) * Bool(Element(x, Interval(-a, a)))))




if __name__ == '__main__':
    run()
# created on 2023-06-18
