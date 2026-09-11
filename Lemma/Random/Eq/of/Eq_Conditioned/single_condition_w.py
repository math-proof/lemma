from util import *


@apply
def apply(given, wrt=None):
    (x, yzw), (S[x], w) = given.of(Equal[Conditioned, Conditioned])
    
    [*args] = yzw.of(And)
    assert w in args
    args.remove(w)

    y, z = args

    if wrt is not None:
        if y.is_Equal:
            y = y.lhs
        if z.is_Equal:
            z = z.lhs

        assert wrt in {y, z}
        return Equal(x | wrt & w, x | w)
    return Equal(x | y & w, x | w)


@prove(proved=False)
def prove(Eq):

    x, y, z, w = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z & w, x | w), wrt=y)


if __name__ == '__main__':
    run()

# created on 2021-07-14
