from util import *



@apply
def apply(x_imply_P, y_imply_P):
    p, x = x_imply_P.of(Given)
    q, y = y_imply_P.of(Given)

    return Given(p | q, x | y)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Given(a > 0, x > 0), Given(b > 0, y > 0))

    Eq << Eq[2].reversed

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq[0].reversed, Eq[1].reversed)


if __name__ == '__main__':
    run()
# created on 2019-02-08
