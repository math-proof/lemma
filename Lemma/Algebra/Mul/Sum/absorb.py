from util import *


@apply
def apply(self, index=1):
    for i, sgm in enumerate(self.args):
        if isinstance(sgm, Sum):
            args = [*self.args]
            args[i] = S.One
            variables_set = sgm.variables_set
            duplicate_set = set()
            for a in args:
                duplicates = {v for v in variables_set if a._has(v)}
                if duplicates:
                    variables_set -= duplicates
                    duplicate_set |= duplicates

            if duplicate_set:
                excludes = set()
                for v in duplicate_set:
                    _v = self.generate_var(excludes=excludes, **v.type.dict)
                    sgm = sgm.limits_subs(v, _v)
                    excludes.add(_v)

            args[i] = sgm.expr
            if i == index:
                if i + 1 < len(self.args):
                    index = i + 1
                elif i > 1:
                    index = 1
                elif i > 0:
                    index = 0
                else:
                    return

            array = [args[index], args[i]]
            del args[i]
            del args[index]
            coeff = Mul(*args)
            return Equal(self, coeff * Sum(self.func(*array).powsimp(), *sgm.limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply(-Sum[k:n](f(k)) * x, 1)

    Eq << Eq[-1].this.rhs.simplify()
    Eq << Eq[-1].this.lhs.apply(Finset.Mul_Sum.eq.Sum_Mul)




if __name__ == '__main__':
    run()
# created on 2023-03-17
