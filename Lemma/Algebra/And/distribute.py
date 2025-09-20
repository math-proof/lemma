from util import *


@apply(given=False)
def apply(self, index=0):
    [*args] = self.of(And)
    factor = args.pop(index)

    for i, ou in enumerate(args):
        if ou.is_Or:
            break
    else :
        return

    args[i] = Or(*(arg & factor for arg in ou.args))
    return And(*args)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, c, d, e, f, x, y = Symbol(real=True)
    Eq << apply(((a < b) | (e < f)) & (c < d) & (x < y), 1)

    Eq << Eq[0].this.find(Or[And]).apply(Algebra.Or.collect, cond=x < y)





if __name__ == '__main__':
    run()
# created on 2021-12-17
# updated on 2023-05-14
