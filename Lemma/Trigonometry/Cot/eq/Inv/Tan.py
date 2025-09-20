from util import *


@apply
def apply(self):
    x = self.of(cot)
    return Equal(self, 1 / tan(x))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(cot(x))

    
    


if __name__ == '__main__':
    run()
# created on 2023-10-03
# updated on 2023-11-26
