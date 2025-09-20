from util import *


def toStack(self, expr, deep=False):
    variables = self.variables

    hit = False
    if expr.shape:
        size = min(len(expr.shape), len(variables))
        variables = variables[:size]
        expr = expr[variables[::-1]]
        if deep:
            if expr.is_Stack:
                expr = toStack(expr, self.expr)
                hit = True
            else:
                try:
                    coeff, (_expr, *limits) = expr.of(Expr * Stack)
                    if not coeff.shape:
                        expr = toStack(Stack(coeff * _expr, *limits), self.expr)
                        hit = True
                except:
                    ...

    if not hit:
        expr += self.expr

    return Stack(expr, *self.limits)

@apply
def apply(self, deep=False):
    [*args] = self.of(Add)
    for i, lamda in enumerate(args):
        if lamda.is_Stack:
            del args[i]
            rhs = toStack(lamda, Add(*args), deep=deep)
            break
    else:
        for i, lamda in enumerate(args):
            lamda = lamda.of(-Stack)
            if lamda:
                expr, *limits = lamda
                lamda = Stack(-expr, *limits)
                del args[i]
                rhs = toStack(lamda, Add(*args), deep=deep)
                break
        else:
            return

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(n, n), integer=True)
    Eq << apply(Stack[i:n, j:n](f(j, i)) + g)

    i, j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)





if __name__ == '__main__':
    run()
# created on 2018-04-04
# updated on 2021-11-21
