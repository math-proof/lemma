from util import *


def equate(*args):
    return And(*[Equal(args[i - 1], args[i]) for i in range(1, len(args))])

@apply
def apply(et_eq, model):
    eqs = et_eq.of(And[Equal[len(et_eq.args)]])
    args = And.connected_equations(eqs)
    assert model in args
    args.remove(model)
    return tuple(Equal(x, model) for x in args)


@prove
def prove(Eq):
    from Lemma import Logic

    λ_1, λ_2, λ_3, λ_4, λ_5, λ_6, λ_7 = Symbol(real=True)
    λ_1_sharp = Symbol(r"λ_{{^\#}1}", real=True)
    λ_2_sharp = Symbol(r"λ_{{^\#}2}", real=True)
    λ_4_sharp = Symbol(r"λ_{{^\#}4}", real=True)
    λ_5_sharp = Symbol(r"λ_{{^\#}5}", real=True)
    λ_6_sharp = Symbol(r"λ_{{^\#}6}", real=True)
    Eq << apply(equate(λ_1_sharp / λ_1, λ_2_sharp / λ_2, λ_4_sharp / λ_4, λ_5_sharp / λ_5, λ_6_sharp / λ_6), λ_1_sharp / λ_1)

    Eq << Logic.And_And.of.And.apply(Eq[0], None)

    Eq << Eq[-4].reversed

    Eq << Eq[-3].subs(Eq[1]).reversed

    Eq << Eq[-2].subs(Eq[2]).reversed

    Eq << Eq[-1].subs(Eq[3]).reversed





if __name__ == '__main__':
    run()
# created on 2021-11-24
