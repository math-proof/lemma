from util import *


@apply
def apply(given):
#     i0 + di * r < min(l * r + i0, s)
#     di < min(-1 // r + l, (s - i0 - 1) // r) + 1
    lhs, rhs = given.of(Less)

    i0, di_r = lhs.of(Add)
    if not di_r.is_Mul:
        i0, di_r = di_r, i0
    di, r = di_r.of(Mul)

    s, lr_i0 = rhs.of(Min)
    if not lr_i0.is_Add:
        s, lr_i0 = lr_i0, s

    lr, _i0 = lr_i0.of(Add)
    if i0 != _i0:
        lr, _i0 = _i0, lr

    assert _i0 == i0

    l, _r = lr.of(Mul)
    if _r != r:
        l, _r = _r, l

    assert _r == r

    return LessEqual(di, Min(-1 // r + l, (s - i0 - 1) // r))


@prove
def prove(Eq):
    from Lemma import Algebra

    di = Symbol('d_i', integer=True)
    i0 = Symbol(integer=True)
    r, l, s = Symbol(integer=True, positive=True)
    Eq << apply(i0 + di * r < Min(l * r + i0, s))

    Eq << Eq[0] - i0

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1] / r

    Eq << Algebra.LeFloor.of.Le.integer.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Floor.eq.Min)

    Eq << Eq[-1].this.rhs.args[0].arg.expand()




if __name__ == '__main__':
    run()
# created on 2019-12-29
# updated on 2023-05-20
