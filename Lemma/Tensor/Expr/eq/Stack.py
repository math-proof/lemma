from util import *

def rewrite(self, *vars):
    assert self.shape

    limits = []
    if vars:
        assert len(vars) <= len(self.shape)
        for j, m in zip(vars, self.shape):
            assert j.is_integer
            assert not self._has(j)
            if m.is_infinite:
                limits.append((j,))
            else:
                limits.append((j, 0, m))
    else:
        excludes = set()
        vars = []
        for m in self.shape:
            j = self.generate_var(excludes, integer=True)
            limits.append((j, 0, m))
            vars.append(j)
            excludes.add(j)

    limits.reverse()
    return Stack(self[tuple(vars)], *limits)


@apply
def apply(self, *vars):
    return Equal(self, rewrite(self, *vars), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    p, q, n, m = Symbol(integer=True, positive=True)
    Y = Symbol(shape=(p, q, m, n), real=True)
    Eq << apply(Y)

    i = Symbol(domain=Range(p))
    k = Symbol(domain=Range(q))
    h = Symbol(domain=Range(m))
    t = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], k)

    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], h)

    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], t)





if __name__ == '__main__':
    run()
# created on 2019-05-08
# updated on 2023-04-14
