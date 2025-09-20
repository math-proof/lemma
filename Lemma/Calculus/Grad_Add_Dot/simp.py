from util import *


def extract_simple_term(self, x):
    if args := self.of(MatMul):
        if args[0] == x:
            b = MatMul(*args[1:])
        elif args[-1] == x:
            b = MatMul(*args[:-1])
        else:
            return

        if not b._has(x):
            return b
@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative)
    assert x.shape
    if fx.is_Add:
        for i, arg in enumerate(fx.args):
            if b := extract_simple_term(arg, x):
                break
        else:
            return
        [*args] = fx.args
        del args[i]
        assert not Add(*args)._has(x)
    else:
        b = extract_simple_term(fx, x)
        if not b:
            return

    return Equal(self, b)


@prove
def prove(Eq):
    from Lemma import Discrete, Calculus, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    f = Function(real=True, shape=())
    c = Symbol(real=True)
    b = Symbol(r"\vec b", real=True, shape=(n,))
    Eq << apply(Derivative(c + b @ x, x))

    Eq << Eq[0].this.find(MatMul).apply(Tensor.Dot.eq.Sum, var='j')

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.eq.Stack)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Add, simplify=None)

    Eq << Eq[-1].this.find(Derivative).doit(deep=False, simplify=None)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.Dot)


    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Eye)




if __name__ == '__main__':
    run()
# created on 2021-12-25
# updated on 2023-04-01

