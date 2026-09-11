from util import *


@apply
def apply(given):
    (x, y), S[x] = given.of(Equal[Conditioned])

    return Equal(Pr(x, y), Pr(x) * Pr(y))


@prove
def prove(Eq):
    from Lemma import Random

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, x))

    Eq << Random.EqPr.of.Eq.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.lhs.apply(Random.Pr.eq.Div.Pr.bayes)



    Eq << Eq[-1] * Pr(y)




if __name__ == '__main__':
    run()
# created on 2020-12-14

# updated on 2023-04-19
