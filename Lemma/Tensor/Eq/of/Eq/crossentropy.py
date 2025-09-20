from util import *


@apply
def apply(given, x):
    expr, limit = given.of(Equal[Sum, 1])

    if len(limit) == 1:
        j = limit[0]
        a, b = expr.domain_defined(j).of(Range)
    else:
        j, a, b = limit

    n = b - a

    t = Stack[j:n](expr).simplify()
    assert n >= 2
    y = softmax(x)
    return Equal(Derivative[x](crossentropy(t, y)), y - t)


@prove
def prove(Eq):
    from Lemma import Discrete, Calculus, Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    t, x = Symbol(shape=(n,), real=True)
    j = Symbol(integer=True)
    Eq << apply(Equal(Sum[j](t[j]), 1), x)

    Eq << Eq[-1].lhs.expr.this.defun()

    y = Symbol(Eq[-1].find(softmax))
    Eq.y_def = y.this.definition

    Eq << Eq[-1].subs(Eq.y_def.reversed)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Sum, var=j)

    i = Symbol(domain=Range(n))
    Eq << Eq[-1].apply(Calculus.EqGrad.of.Eq, (x[i],), simplify=False)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Mul)

    Eq.loss = Eq[-1].this.find(Derivative[Sum]).apply(Calculus.Grad.eq.Sum)

    Eq << Eq.y_def[i]

    Eq << Eq.y_def[j]

    Eq << Eq[-1].apply(Calculus.EqGrad.of.Eq, (x[i],), simplify=False)

    Eq << Eq[-1].this.rhs.doit(deep=False)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(Calculus.Grad.eq.Mul.Grad)

    Eq << Eq[-1].subs(Eq[-4].reversed).subs(Eq[-5].reversed) / Eq[-1].lhs.expr

    Eq << Eq.loss.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[0].simplify()

    Eq << Eq[-1].this.rhs.args[1].args[1].simplify()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i,))

    Eq << Eq[-1].subs(Eq.y_def)





if __name__ == '__main__':
    run()
# created on 2020-12-27
# updated on 2023-03-19
