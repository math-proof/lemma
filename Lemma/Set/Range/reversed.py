from util import *


@apply
def apply(self):
    a, b, k = self.of(Range)
    b -= sign(k)
    return Equal(self, Range(b - (b - a) % k, a - sign(k), -k))


@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(integer=True)
    k = Symbol(integer=True, zero=False)
    Eq << apply(Range(a, b, k))

    Eq << Equal(a + k * (Ceil((b - a) / k) - 1), (b - sign(k)) - (b - sign(k) - a) % k, plausible=True)

    Eq << Eq[1] - a

    c = Symbol(b - a)
    Eq << c.this.definition

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub_Mul_Div)

    Eq << Eq[-1].this.find(Ceil).apply(Algebra.Ceil.eq.Add.Floor)

    Eq << Eq[0].subs(Eq[1].reversed)




if __name__ == '__main__':
    run()
# created on 2023-05-29
