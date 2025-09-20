from util import *


@apply
def apply(self):
    for i, union in enumerate(self.args):
        if isinstance(union, Cup):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            function = union.expr & this
            return Equal(self, union.func(function, *union.limits), evaluate=False)


@prove
def prove(Eq):
    x = Symbol(etype=dtype.integer)
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cup[k:n](f(k)) & x)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2021-02-09
