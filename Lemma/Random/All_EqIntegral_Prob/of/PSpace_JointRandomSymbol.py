from util import *



@apply
def apply(self):
    from Lemma.Random.Sum.eq.Prob import marginalize
    return Equal(self, marginalize(Integral, self))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Pr(x, y)))


if __name__ == '__main__':
    run()
# created on 2020-12-07
# updated on 2023-03-27
