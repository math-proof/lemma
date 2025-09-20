from util import *


def append_coeffs(mat, coeffs):
    mat = Add(*mat)
    if coeffs:
        coeffs = Add(*coeffs)
        coeffs *= Identity(mat.shape[-1])
        mat += coeffs

    return mat

def extract(self):
    args = self.of(Add)
    multiplicants = []
    coefficients = []
    for arg in args:
        if multiplicant := arg.of(MatMul):
            coefficient = 1
        elif arg.is_Mul:
            if ret := arg.of(Expr * MatMul):
                coefficient, multiplicant = ret
            else:
                return
        else:
            multiplicant = (arg,)
            coefficient = 1

        coefficients.append(coefficient)
        multiplicants.append(multiplicant)

    size = min(len(factor) for factor in multiplicants)

    return coefficients, multiplicants, size

def factor_lhs(coefficients, multiplicants, size):
    for i in range(size):
        if len({factor[i] for factor in multiplicants}) != 1:
            break

    if i:
        lhs = MatMul(*multiplicants[0][:i])
        rhs = []
        coeffs = []
        for coeff, factor in zip(coefficients, multiplicants):
            factor = factor[i:]
            if factor:
                rhs.append(coeff * MatMul(*factor))
            else:
                coeffs.append(coeff)

        rhs = append_coeffs(rhs, coeffs)

        return lhs, rhs


def factor_rhs(coefficients, multiplicants, size):
    for i in range(-1, -size - 1, -1):
        if len({factor[i] for factor in multiplicants}) != 1:
            i += 1
            break

    if i:
        rhs = MatMul(*multiplicants[0][i:])
        lhs = []
        coeffs = []
        for coeff, factor in zip(coefficients, multiplicants):
            factor = factor[:i]
            if factor:
                lhs.append(coeff * MatMul(*factor))
            else:
                coeffs.append(coeff)

        lhs = append_coeffs(lhs, coeffs)
        return lhs, rhs


@apply
def apply(self, deep=True):
    multiplicants, coefficients, size = extract(self)

    if ret := factor_lhs(multiplicants, coefficients, size):
        lhs, rhs = ret
        if ret := extract(rhs):
            multiplicants, coefficients, size = ret
            if deep and (ret := factor_rhs(multiplicants, coefficients, size)):
                rhs = MatMul(*ret)

    else:
        lhs, rhs = factor_rhs(multiplicants, coefficients, size)

    return Equal(self, lhs @ rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    x, a, b = Symbol(shape=(n, n), complex=True)
    Eq << apply(x @ a + x @ b)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Add)





if __name__ == '__main__':
    run()
# created on 2021-12-26


from . import Block
