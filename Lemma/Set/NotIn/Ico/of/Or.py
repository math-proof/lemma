from util import *


@apply
def apply(given):
    lt, gt = given.of(Or)
    if not lt.is_Less and not lt.is_LessEqual:
        lt, gt = gt, lt

    e, a = lt.args
    S[e], b = gt.args

    if lt.is_Less:
        left_open = False
    elif lt.is_LessEqual:
        left_open = True

    if gt.is_Greater:
        right_open = False
    elif gt.is_GreaterEqual:
        right_open = True

    return NotElement(e, Range(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set

    e, a, b = Symbol(integer=True, given=True)
    Eq << apply((e < a) | (e >= b))

    Eq <<= Set.NotIn_Ico.given.Or.apply(Eq[1])





if __name__ == '__main__':
    run()
# created on 2021-12-17
