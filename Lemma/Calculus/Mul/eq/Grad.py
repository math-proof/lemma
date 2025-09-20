from util import *



def mul_to_derivative(self):
    for i, derivative in enumerate(self.args):
        if derivative.is_Derivative:
            args = [*self.args]
            del args[i]
            function, *limits = derivative.args
            vars = [v for v, *_ in limits]
            for arg in args:
                assert not arg.has(*vars)
            return Derivative(Mul(function, *args), *limits)


@apply
def apply(self):
    assert self.is_Mul
    return Equal(self, mul_to_derivative(self))


@prove(proved=False)
def prove(Eq):
    x, y = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x)) * y)


if __name__ == '__main__':
    run()

# created on 2020-06-27
