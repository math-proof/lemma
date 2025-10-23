from util import *


@apply
def apply(ne_zero_given, ne_zero_joint):

    vars_given = set()
    given = ne_zero_given.of(Unequal[Pr, 0])
    if conds := given.of(And):
        ...
    else:
        conds = [given]

    for cond in conds:
        x, x_var = cond.of(Equal)
        vars_given.add(x)

    vars_joint = set()
    for cond in ne_zero_joint.of(Unequal[Pr[And], 0]):
        x, x_var = cond.of(Equal)
        vars_joint.add(x)

    vars = vars_joint - vars_given
    return Unequal(Pr(*vars, given=And(*(var.as_boolean() for var in vars_given))), 0)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Nat, Nat, Nat

    x, y = Symbol(random=True, integer=True)
    Eq << apply(Unequal(Pr(y), 0),
                Unequal(Pr(x, y), 0))

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[0], x)

    Eq << Nat.EqDivS.of.Eq.apply(Eq[0], Eq[-1])

    Eq << Algebra.Ne_0.Div.of.Ne_0.Ne_0.apply(Eq[1], Eq[0])

    Eq << Algebra.Ne.of.Ne.Eq.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-03-22
