from util import *


def common_terms(args):
    common_terms = None
    for arg in args:
        if arg.is_Mul:
            if common_terms is None:
                common_terms = {*arg.args}
            else:
                common_terms = Add.intersect_args(common_terms, arg.args)
        else:
            if common_terms is None:
                common_terms = {arg}
            else:
                common_terms = Add.intersect_args(common_terms, [arg])
        if not common_terms:
            return
    return common_terms


def rewrite(self):
    args = self.of(Add)
    if c := common_terms(args):
        args, c = Mul.factorize(args, c)
        return Add(*args), c


@apply
def apply(self):
    return Equal(self, Mul(*rewrite(self)))


@prove
def prove(Eq):
    a, x, y = Symbol(complex=True)
    Eq << apply(a * x - a * y)

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()

# created on 2018-02-21
# updated on 2023-04-30
