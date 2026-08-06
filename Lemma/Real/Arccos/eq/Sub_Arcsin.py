from util import *


@apply
def apply(self):
    x = self.of(acos)
    return Equal(self, S.Pi / 2 - asin(x))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(acos(x))

    Eq << Eq[0].subs(x, 0)

    Eq << Eq[0].subs(x, S.One / 2)

    Eq << Eq[0].subs(x, 1)

    Eq << Eq[0].subs(x, -S.One / 2)
    Eq << Eq[0].subs(x, -1)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)



if __name__ == '__main__':
    run()
# created on 2018-06-13
