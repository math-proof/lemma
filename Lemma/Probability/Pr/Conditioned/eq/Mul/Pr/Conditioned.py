from util import *


@apply
def apply(self, pivot=-1):
    args, given = self.of(Pr[Conditioned[And]])
    x, y = std.array_split(args, pivot)
    x = And(*x)
    y = And(*y)
    return Equal(self, Pr(y, given=x & given) * Pr(x, given=given))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Pr(y & x | z))


    Eq << Eq[0].this.rhs.args[1].apply(Probability.Pr.Conditioned.eq.Div.Pr.Conditioned)



if __name__ == '__main__':
    run()
# created on 2023-10-14
