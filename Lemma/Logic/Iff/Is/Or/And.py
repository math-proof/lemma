from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return (p.invert() & q.invert()) | (p & q)


@prove
def prove(Eq):
    from Lemma import Logic

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Logic.Iff.Is.And.Or)

    Eq << Eq[-1].this.lhs.apply(Logic.And_Or.Is.OrAndS)




if __name__ == '__main__':
    run()
# created on 2022-01-27
