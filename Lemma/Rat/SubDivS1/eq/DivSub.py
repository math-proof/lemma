from util import *


@apply
def apply(self):
    [*args] = self.of(Add)
    factors = []

    for arg in args:
        if arg.is_Mul:
            factor = []
            for fac in arg.args:
                if fac.is_Pow and fac.exp == -1:
                    factor.append(fac.base)
            if factor:
                factor = Mul(*factor)
                factors.append(factor)
        elif arg.is_Pow:
            if arg.exp == -1:
                factors.append(arg.base)
    assert factors

    from Lemma.Nat.AddMulS.eq.Mul_Add import common_terms
    if c := common_terms(factors):
        factors, c = Mul.factorize(factors, c)
        factor = Mul(*factors) * c
    else:
        factor = Mul(*factors)

    for i in range(len(args)):
        args[i] *= factor

    num = Add(*args)
    rhs = Mul(num, 1 / factor)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    a, b = Symbol(complex=True)
    Eq << apply(1 / a - 1 / b)

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2018-07-21
