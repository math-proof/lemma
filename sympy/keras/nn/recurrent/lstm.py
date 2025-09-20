from sympy.tensor.indexed import Sliced
from sympy.keras.nn import sigmoid
from sympy.functions.elementary.hyperbolic import tanh
from sympy.matrices.expressions.blockmatrix import BlockMatrix
from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Zeros
from sympy.concrete.expr_with_limits import Stack
from sympy.core.symbol import Symbol
from sympy.core.function import Function
from sympy.core.containers import Tuple

@property
def shape(self):
    (Wh,) = self.limits[1]
    d = Wh.shape[-1] / 4
    if len(self.limits) > 3:
        return (2 * d,)
    
    x = self.arg
    x_shape = x.shape
    shape = (x_shape[-2], d)
    if len(x_shape) > 2:
        shape = (x[0],) + shape
    return shape


@Function(real=True, integer=None, shape=shape)
def lstm(x, *limits):
    (W,), (Wh,), (b,), (t,) = limits
    hc = lstm[W, Wh, b, t - 1](x)
    
    xt = x[t]
    
    d = hc.shape[0] / 2
    
    h = Sliced(hc, Tuple(0, d))
    c = Sliced(hc, Tuple(d, 2 * d))    
    d = h.shape[-1]
    
    Wi = W[:,:d]
    Wf = W[:, d:2 * d]
    Wc = W[:, 2 * d:3 * d]
    Wo = W[:, -d:]

    Whi = Wh[:,:d]
    Whf = Wh[:, d:2 * d]
    Whc = Wh[:, 2 * d:3 * d]
    Who = Wh[:, -d:]    
    
    bi = b[:d]
    bf = b[d:2 * d]
    bc = b[2 * d:3 * d]
    bo = b[-d:]

    i = sigmoid(xt @ Wi + h @ Whi + bi)
    f = sigmoid(xt @ Wf + h @ Whf + bf)
    c = f * c + i * tanh(xt @ Wc + h @ Whc + bc)
    o = sigmoid(xt @ Wo + h @ Who + bo)    
     
    return Piecewise((BlockMatrix(o * tanh(c), c), t > 0), (Zeros(*hc.shape), True))

    
@Function(real=True, integer=None, shape=shape)    
def LSTM(x, *weights):
    (W,), (Wh,), (b,) = weights
    n = x.shape[0]
    t = Symbol(integer=True)
    expr = lstm[W, Wh, b, t](x)
    d = expr.shape[0] / 2
    return Stack[t:n](Sliced(lstm[W, Wh, b, t](x), Tuple(0, d)))


@Function(real=True, integer=None, shape=shape)
def LSTMCell(x, *weights):
    (W,), (Wh,), (b,) = weights
    n = x.shape[0]
    t = Symbol(integer=True)
    expr = lstm[W, Wh, b, t](x)
    d = expr.shape[0] / 2
    return Stack[t:n](Sliced(expr, Tuple(d, d * 2)))

