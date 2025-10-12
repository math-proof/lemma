from util import *


def rewrite(Sum, self):
    for i, sgm in enumerate(self.of(Mul)):
        if isinstance(sgm, Sum):
            break
    else:
        return

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
    return Sum(self.func(*args).powsimp(), *sgm.limits)

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self))


@prove
def prove(Eq):
    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply(Sum[k:n](f(k)) * x)

    Eq << Eq[-1].this.rhs.simplify()




if __name__ == '__main__':
    run()

# created on 2018-02-14
# updated on 2023-03-28
