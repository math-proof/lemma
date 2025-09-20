from util import *


@apply
def apply(self, coeff=None):
    blocks = self.of(BlockMatrix)

    if coeff is None:
        common_terms = None
        for block in blocks:
            if block.is_Add:
                if common_terms is None:
                    common_terms = {*block.args}
                else:
                    common_terms &= {*block.args}
            else:
                if common_terms is None:
                    common_terms = {block}
                else:
                    common_terms &= {block}
        if common_terms:
            args = []
            for e in self.args:
                if e.is_Add:
                    e = Add(*{*e.args} - common_terms)
                else:
                    e = Zeros(*e.shape)
                args.append(e)
            coeff = Add(*common_terms)
            assert len(coeff.shape) < len(self.shape)
            rhs = coeff + BlockMatrix(*args)

    else:
        ec = [e + coeff for e in blocks]
        rhs = Add(BlockMatrix(*ec), -coeff)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    A, B, C = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix(A + x, B + x, C + x))

    i = Symbol(domain=Range(n * 3))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.SubIte)





if __name__ == '__main__':
    run()
# created on 2021-12-20
