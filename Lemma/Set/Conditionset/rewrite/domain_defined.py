from util import *

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(self):
    cond = self.condition
    variable = self.variable
    domain_defined = cond.domain_defined(variable)
    return Equal(self, conditionset(variable, cond, domain_defined), evaluate=False)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))

    f = Function(real=True)
    i = Symbol(integer=True)

    Eq << apply(conditionset(i, f(x[i]) > 0))

    Eq << Eq[0].this.rhs.simplify()


if __name__ == '__main__':
    run()

# created on 2020-12-22
