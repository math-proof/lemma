from util import *


@apply
def apply(self):
    k, args = self.of(relu[Expr - Min])

    hit = False
    rest = []
    for arg in args:
        if k <= arg:
            hit = True
            continue
        rest.append(arg)
    assert hit
    return Equal(self, relu(k - Min(*rest)))


@prove
def prove(Eq):
    from Lemma import Tensor

    n, l = Symbol(integer=True)
    k = Symbol(domain=Range(-oo, n + 1))
    Eq << apply(relu(k - Min(l, n)))

    Eq << LessEqual(k, n, plausible=True)

    Eq << Tensor.EqRelu.of.Le.apply(Eq[1], l)



if __name__ == '__main__':
    run()
# created on 2021-12-25
