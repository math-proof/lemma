from util import *


@apply
def apply(self):
    from Lemma.Calculus.Mul.eq.Grad import mul_to_derivative
    args = self.of(Add)
    funcs = []
    limits = None
    for arg in args:
        if arg.is_Mul:
            arg = mul_to_derivative(arg)

        function, *limits_d = arg.of(Derivative)
        funcs.append(function)
        if limits is None:
            limits = limits_d
        else:
            assert limits_d == limits


    return Equal(self, Derivative(Add(*funcs), *limits))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x)) - Derivative[x](g(x)))


if __name__ == '__main__':
    run()

# created on 2020-06-11
