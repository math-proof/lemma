from util import *


@apply
def apply(self):
    args = self.of(Add)

    logs = []
    for arg in args:
        if arg.is_Log:
            logs.append(arg.arg)
        else:
            [*_args] = arg.of(Mul)
            log_x = None
            for i, log_x in enumerate(_args):
                if log_x.is_Log:
                    break
            else:
                return
            del _args[i]
            coeff = Mul(*_args)
            assert coeff.is_odd
            logs.append(log_x.arg ** coeff)

    rhs = log(Mul(*logs), evaluate=False)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Real

    a, b = Symbol(real=True)
    Eq << apply(Log(a) - Log(b))

    Eq << Real.Eq.given.EqExpS.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-05
