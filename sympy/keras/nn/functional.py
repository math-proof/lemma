from sympy.core.function import Function
from sympy.core.symbol import Symbol
from sympy.concrete.expr_with_limits import Stack
from sympy.functions.elementary.miscellaneous import Max, Min
from sympy.concrete.summations import Sum
from sympy.concrete.reduced import ReducedMean
from sympy.core.power import sqrt

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


def one_hot(x, units):
    return x

def conv1d_shape(self):
    x, w, *limits = self.args
    return x.shape[:-1] + w.shape[-1:]

def initial_offset(r, w, i=0):
    return (w.shape[i] - 1) // 2 * r[i] + (r[i] // 2) * (1 - w.shape[i] % 2)

def sum_limit(dilation, kernel_shape, seq_length, di, i0, index=0):
    return slice(di, Max(0, -(i0 // dilation[index])), Min(-1 // dilation[index] + kernel_shape[index], (seq_length - i0 - 1) // dilation[index]) + 1)

def conv1d(x, w, b, stride=1, padding=0, dilation=1, groups=1):
    """
    >>> m = Symbol(integer=True, positive=True)
    >>> n = Symbol(integer=True, positive=True)
    >>> d = Symbol(integer=True, positive=True)
    >>> x = Symbol(real=True, shape=(m, n, d))
    >>> d_ = Symbol("d'", integer=True, positive=True)
    >>> l = Symbol(integer=True, positive=True)
    >>> w = Symbol(real=True, shape=(l, d, d_))
    >>> r = Symbol(integer=True, positive=True)
    >>> conv1d[r](x, w).this.defun()
    """    
    *kernel_size, in_channels, out_channels = w.shape
    batch_size, seq_length, _in_channels = x.shape
    
    assert in_channels * groups == _in_channels

    excludes = w.free_symbols | b.free_symbols
    k = x.generate_var(integer=True, var='k', exludes=excludes)
    excludes.add(k)
    
    i = x.generate_var(integer=True, var='i', exludes=excludes)
    excludes.add(i)
    
    di = x.generate_var(integer=True, var='d_i', exludes=excludes)
    excludes.add(di)
    
    if isinstance(padding, tuple):
        padding = padding[0]
        
    if isinstance(stride, tuple):
        stride = stride[0]
        
    i0 = i - padding
    
    return Stack[i:(seq_length + 2 * padding - dilation[0] * (kernel_size[0] - 1) - 1 + stride) // stride, 
                 k:batch_size](
        Sum[sum_limit(dilation, kernel_size, seq_length, di, i0)](
            x[k, i0 + di * dilation[0]] @ w[di] + b))


def layer_norm(input, weight, bias, epsilon):
    embed_size = input.shape[-1]
    mean = ReducedMean(input).unsqueeze(-1, embed_size)
    deviation = input - mean
    return deviation / sqrt(ReducedMean(deviation ** 2) + epsilon).unsqueeze(-1, embed_size) * weight + bias
