from util import *


def from_MinMaxBase(self):
    common_terms = None

    for plus in self.args:
        if isinstance(plus, Add):
            if common_terms is None:
                common_terms = {*plus.args}
            else:
                common_terms &= {*plus.args}
        else:
            if common_terms is None:
                common_terms = {plus}
            else:
                common_terms &= {plus}
    if common_terms:
        args = []
        for e in self.args:
            if isinstance(e, Add):
                e = Add(*{*e.args} - common_terms)
            elif e.is_Zero:
                ...
            else:
                e = 0
            args.append(e)
        return Add(*common_terms, self.func(*args))

@apply
def apply(self):
    self.of(Max)

    return Equal(self, from_MinMaxBase(self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)
    r = Symbol(real=True, positive=True)

    Eq << apply(Max(x * r + 1, y * r + 1))

    Eq << Eq[-1].this.lhs.apply(Algebra.Max.eq.IteGe)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.SubIte)

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.IteGe)

if __name__ == '__main__':
    run()
# created on 2019-03-10
