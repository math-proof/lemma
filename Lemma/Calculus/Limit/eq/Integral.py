from util import *



@apply
def apply(self, *, simplify=True):
    from Lemma.Calculus.Limit.eq.Sum import doit
    return Equal(self, doit(Integral, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True)
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Limit[n:oo](Integral[x:a:b](f[n](x))))




if __name__ == '__main__':
    run()
# created on 2023-04-04
