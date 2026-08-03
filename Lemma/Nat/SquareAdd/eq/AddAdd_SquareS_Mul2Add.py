from util import *


@apply
def apply(self):
    args = self.of(Add ** 2)
    square = []
    for x in args:
        square.append(x ** 2)

    n = len(args)
    mutual_pairs = []
    for i in range(1, n):
        for j in range(0, i):
            mutual_pairs.append(args[i] * args[j] * 2)

    return Equal(self, Add(*square, *mutual_pairs))


@prove
def prove(Eq):
    x, y, z = Symbol(real=True)
    Eq << apply((x + y + z) ** 2)

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()

# created on 2018-06-06
