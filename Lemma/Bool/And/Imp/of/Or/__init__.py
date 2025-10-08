from util import *

def check_validity(eqs, x, i):
    last = eqs[-1][x[i]]
    for j, index in enumerate(x[:i]):
        if (eqs[j][index] & last).is_BooleanFalse:
            continue
        else:
            return False
    return True

# return a combination of k elements selected among {0, 1, 2, n - 2, n - 1};
def detect_nonoverlapping_conds(eqs):
    k = len(eqs)

    x = [0] * k
    i = 0
    while True:
        assert x[i] < len(eqs[i])
        if i == k - 1:
            return x

        i += 1
        x[i] = 0
        while not check_validity(eqs, x, i):
            x[i] += 1
            if x[i] >= len(eqs[i]):
                break
        else:
            # ensure that x[:i] and x[i] are coherent before continue
            continue
        # if in current position i, we couldn't find a feasible cond, it is possible to revert back and try again.
        i -= 1
        x[i] += 1  # backtracking to the previous index.
        while not check_validity(eqs, x, i):
            x[i] += 1
            if x[i] >= len(eqs[i]):
                break
        else:
            # backtracking has succeeded, continue with the next position!
            continue

        # backtracking has failed return None
        break

@apply
def apply(given, pivot=None):
    or_eqs = given.of(boolalg.Or)
    eqs = [[*ou.of(And)] for ou in or_eqs]
    if pivot is None:
        pivot = detect_nonoverlapping_conds(eqs)

    result = []
    for i, eqs in enumerate(eqs):
        index = pivot[i]
        given = eqs[index]
        del eqs[index]
        imply = And(*eqs)
        result.append(Imply(given, imply))

    return tuple(result)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a, b, c, d = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(boolalg.Or(Equal(b, 0) & Equal(c, 0) & Equal(d, 0) & Equal(f(x), 0), Equal(c, 0) & Equal(d, 0) & Equal(a, 0) & Equal(f(x), 1), Equal(a, 0) & Equal(b, 0) & Equal(d, 0) & Equal(f(x), 2), Equal(a, 0) & Equal(b, 0) & Equal(c, 0) & Equal(f(x), 3)))

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Equal(f(x), 0))

    Eq << Bool.ImpEq.of.ImpEq.subst.apply(Eq[-1])

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Equal(f(x), 1))

    Eq << Bool.ImpEq.of.ImpEq.subst.apply(Eq[-1])

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Equal(f(x), 2))

    Eq << Bool.ImpEq.of.ImpEq.subst.apply(Eq[-1])

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Equal(f(x), 3))

    Eq << Bool.ImpEq.of.ImpEq.subst.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-11-24


del Or
from . import Or
