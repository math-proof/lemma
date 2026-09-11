from util import *


@apply
def apply(self):
    cond, given = self.of(Pr[Conditioned])
    return Equal(self, Pr(cond & given) / Pr(given))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    Eq << apply(Pr(x | y))


if __name__ == '__main__':
    run()

# created on 2020-12-09
