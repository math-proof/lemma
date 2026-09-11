from util import *


def subs(self, *limits):
    if self.is_Probability:
        expr, = self.args
        return Pr(expr, *limits)
    else:
        args = [subs(arg, *limits) for arg in self.args]
        kwargs = self.kwargs
        return self.func(*args, **kwargs)

@apply
def apply(given, *limits):
    return subs(given, *limits)


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n,), random=True)
    θ = Symbol(real=True, shape=(n,))
    Eq << apply(Unequal(Pr(x, y), 0), (x, θ))

    


if __name__ == '__main__':
    run()
# created on 2023-04-05
