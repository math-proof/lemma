from util import *


@apply
def apply(self, ρ=None, θ=None):
    if ρ is None:
        ρ = Symbol(real=True)
    if θ is None:
        θ = Symbol(real=True)

    _x = ρ * cos(θ)
    _y = ρ * sin(θ)

    J = Matrix([_x, _y]).jacobian(Matrix([ρ, θ])).det().trigsimp()

    (x,), (y,) = self.limits
    function = self.expr.subs({x:_x, y:_y}, simultaneous=True).trigsimp()
    rhs = Integral[ρ:0:oo, θ:-pi:pi] (J * function)

    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    x, y = Symbol(real=True)
    Eq << apply(Integral[x, y](E ** (-x ** 2 / 2 - y ** 2 / 2)))

    # https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/
    


if __name__ == '__main__':
    run()
# created on 2020-06-09
# updated on 2023-04-30
