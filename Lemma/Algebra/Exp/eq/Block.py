from util import *


def rewrite(self):
    arg = self.of(Exp)
    if arg is None:
        return self

    if arg.is_Mul:
        [*args] = arg.args
        for i, block in enumerate(args):
            if block.is_BlockMatrix:
                break
        else:
            return self

        del args[i]
        e = Mul(*args)
        args = block.args
        args = [exp(b * e) for b in args]
        axis = block.axis

    elif arg.is_BlockMatrix:
        args = arg.args
        axis = arg.axis
        args = [rewrite(exp(e)) for e in args]

    else:
        return self

    return BlockMatrix[axis](args)

@apply
def apply(self):
    return Equal(self, rewrite(self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Real, Real

    a, b, n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(a, n))
    B = Symbol(real=True, shape=(b, n))
    Eq << apply(exp(BlockMatrix(A, B)))

    i = Symbol(domain=Range(a + b))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Real.ExpIte.eq.Ite_ExpS)




if __name__ == '__main__':
    run()
# created on 2021-12-19
# updated on 2023-06-08
