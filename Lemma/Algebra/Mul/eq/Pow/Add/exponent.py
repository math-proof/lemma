from util import *


def determine_args(args):
    b2e = {}
    others = []
    for arg in args:
        if arg.is_Pow:
            b, e = arg.args
            if b not in b2e:
                b2e[b] = []
            b2e[b].append(e)

        elif arg in b2e:
            b2e[arg].append(1)

        else:
            others.append(arg)

    indices_to_delete = []
    for i, other in enumerate(others):
        if other in b2e:
            indices_to_delete.append(i)
            b2e[other].append(1)
            break

    if indices_to_delete:
        indices_to_delete.reverse()
        for i in indices_to_delete:
            del others[i]

    return Mul(*(base ** Add(*exponent) for base, exponent in b2e.items())), others

@apply
def apply(self):
    ret, others = determine_args(self.of(Mul))
    assert not others
    return Equal(self, ret, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, t = Symbol(real=True)
    Eq << apply(t ** x * t ** y)

    Eq << Eq[-1].this.rhs.apply(Algebra.Pow.eq.Mul.split.exponent)





if __name__ == '__main__':
    run()

# created on 2020-01-30
# updated on 2022-07-07
