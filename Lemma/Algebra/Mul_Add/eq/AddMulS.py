from util import *


def convert(self, i=None, deep=False, simplify=True):
    [*args] = self.of(Mul)
    if i is None:
        for i, arg in enumerate(args):
            if arg.is_Add:
                break
        else :
            return self
    else :
        arg = args[i]

    summand = []
    for e in arg.args:
        _args = [*args]
        _args[i] = e
        prod = Mul(*_args)
        if deep and prod.is_Mul:
            prod = convert(prod, deep=deep, simplify=simplify)
        summand.append(prod)

    summand = Add(*summand)
    if simplify:
        summand = summand.simplify()
    return summand


@apply
def apply(self, i=None, deep=False, *, simplify=True):
    rhs = convert(self, i, deep=deep, simplify=simplify)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    x, a, b = Symbol(complex=True)
    Eq << apply(x * (a + b))

    Eq << Eq[-1].this.lhs.expand()





if __name__ == '__main__':
    run()

# created on 2018-03-01
# updated on 2022-01-15
