from util import *


@apply
def apply(self):
    [*args] = self.of(And)

    for i, infer in enumerate(args):
        if isinstance(infer, Imply):
            del args[i]
            r = And(*args)
            break
    else:
        return

    p, q = infer.args
    return Imply(p | r.invert(), q & r, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Logic

    p, q, r = Symbol(bool=True)
    Eq << apply(And(Imply(p, q), r))

    Eq << Eq[0].this.find(Imply).apply(Logic.Imp.Is.Or_Not)

    Eq << Eq[-1].this.apply(Logic.And_Or.Is.OrAndS)

    Eq << Eq[-1].this.apply(Logic.Or.Is.Imp, 1)




if __name__ == '__main__':
    run()
# created on 2023-04-05
