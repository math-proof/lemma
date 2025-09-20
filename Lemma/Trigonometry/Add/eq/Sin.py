from util import *


@apply
def apply(self):
    (x, y), (S[y], S[x]) = self.of(Sin * Cos + Sin * Cos)
    return Equal(self, sin(x + y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x) * cos(y) + cos(x) * sin(y))

    Eq << Eq[0].this.rhs.apply(Trigonometry.Sin.eq.Add)



if __name__ == '__main__':
    run()
# created on 2023-06-01

