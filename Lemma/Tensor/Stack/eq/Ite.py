from util import *


@apply
def apply(self):
    ecs, *limits = self.of(Stack[Piecewise])

    variables = self.variables
    args = []
    for e, c in ecs:
        assert not c._has(*variables)
        args.append((Stack(e, *limits).simplify(), c))

    rhs = Piecewise(*args)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, a = Symbol(integer=True)
    j = Symbol(integer=True, given=True)
    n = Symbol(integer=True, positive=True)
    g, h = Symbol(shape=(n, n), real=True)
    Eq << apply(Stack[i:n](Piecewise((g[i, j], j < a),(h[i, j], True))))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-19
