from util import *


def rewrite(cls, self):
    x = self.of(cls)
    if x.is_Mul:
        [*args] = x.args
        for i, arg in enumerate(args):
            if arg.is_Add:
                args[i] = -arg
                break
        else:
            args.append(S.NegativeOne)

        x = Mul(*args)
    else:
        x = -x
    return -cls(x)

@apply
def apply(self):
    return Equal(self, rewrite(sinh, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(complex=True)
    Eq << apply(sinh(x - y))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Sinh.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sinh).apply(Trigonometry.Sinh.eq.Add)




if __name__ == '__main__':
    run()
# created on 2023-11-26
