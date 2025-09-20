from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Zeros
from sympy.keras.nn import sigmoid
from sympy.functions.elementary.hyperbolic import tanh
from sympy.core.function import Function
from sympy.core.symbol import Symbol
from sympy.concrete.expr_with_limits import Stack

@property
def shape(self):
    (Wh,) = self.limits[1]
    d = Wh.shape[-1] / 3
    if len(self.limits) > 3:
        return (d,)
    
    x = self.arg
    x_shape = x.shape
    shape = (x_shape[-2], d)
    if len(x_shape) > 2:
        shape = (x[0],) + shape
    return shape


@Function(real=True, shape=shape)
def gru(x, *limits):    
    (Wx,), (Wh,), (b,), (t,) = limits
    h = gru[Wx, Wh, b, t - 1](x)

    d = h.shape[-1]

    xt = x[t]    
    Wxz = Wx[:, :d]
    Wxr = Wx[:, d:2 * d]
    Wxh = Wx[:, -d:]
    
    Whz = Wh[:, :d]
    Whr = Wh[:, d:2 * d]
    Whh = Wh[:, -d:]
    
    bz = b[:d]
    br = b[d:2 * d]
    bh = b[-d:]
 
    z = sigmoid(xt @ Wxz + h @ Whz + bz) 
    r = sigmoid(xt @ Wxr + h @ Whr + br)     
    gh = tanh(xt @ Wxh + (r * h) @ Whh + bh)
    
    return Piecewise(((1 - z) * gh + z * h, t > 0), (Zeros(*h.shape), True))


@Function(real=True, shape=shape)
def GRU(x, *limits):
    (Wx,), (Wh,), (b,) = limits
    n = x.shape[0]
    t = Symbol(integer=True)
    return Stack[t:n](gru[Wx, Wh, b, t](x))

