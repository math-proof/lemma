from util import *

def determine_args(args, simplify):
    e2b = {}

    others = []
    for arg in args:
        if arg.is_Pow:
            b, e = arg.args
            if e not in e2b:
                if -e in e2b:
                    if e._coeff_isneg():
                        e2b[-e].append(1 / b)
                    else:
                        e2b[e] = [b, *[1 / b for b in e2b[-e]]]
                        del e2b[-e]
                    continue
                e2b[e] = []
            e2b[e].append(b)
        else:
            others.append(arg)

    indices_to_delete = []
    for i, arg in enumerate(others):
        if arg.is_Rational and arg > 0:
            for e in e2b:
                b = arg ** (1 / e)
                if b.is_Rational:
                    indices_to_delete.append(i)
                    e2b[e].append(b)
                    break

    if indices_to_delete:
        indices_to_delete.reverse()
        for i in indices_to_delete:
            del others[i]

    for e, bs in e2b.items():
        assert sum(int(not b.is_extended_real) for b in bs) < 2

    args = []
    for e, b in e2b.items():
        arg = Mul(*b)
        if simplify:
            arg = arg.simplify()
        args.append(arg ** e)

    return args, others


@apply
def apply(self, *, simplify=True):
    args, others = determine_args(self.of(Mul), simplify=simplify)
    assert not others
    ret, = args
    return Equal(self, ret, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    t = Symbol(integer=True)
    Eq << apply(x ** t * y ** t)

    Eq << Eq[-1].this.rhs.apply(Algebra.Pow.eq.Mul.split.base)




if __name__ == '__main__':
    run()

# created on 2018-11-13
# updated on 2022-07-07
