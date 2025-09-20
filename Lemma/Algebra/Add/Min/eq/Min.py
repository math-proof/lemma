from util import *


@apply
def apply(self):
    args_lhs, args_rhs = self.of(Min + Min)

    args = []
    for lhs in args_lhs:
        for rhs in args_rhs:
            args.append(lhs + rhs)

    return Equal(self, Min(*args))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z, w = Symbol(real=True)
    Eq << apply(Add(Min(x, y), Min(z, w), evaluate=False))

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.lhs.find(Add[Min]).apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.lhs.find(Add[Min]).apply(Algebra.Add.eq.Min)



if __name__ == '__main__':
    run()
# created on 2023-03-26
