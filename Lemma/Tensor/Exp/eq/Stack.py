from util import *


@apply
def apply(self):
    arg = self.of(Exp)
    if arg.is_Mul:
        [*args] = arg.args
        for i, lamda in enumerate(args):
            if lamda.is_Stack:
                break
        else:
            return
        del args[i]
        coeff = Mul(*args)
        f, *limits = lamda.of(Stack)
        f *= coeff
    else:
        f, *limits = arg.of(Stack)

    return Equal(self, Stack(exp(f), *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    h = Symbol(integer=True, shape=(n,))
    Eq << apply(exp(Stack[i:n](h[i])))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-12-19
