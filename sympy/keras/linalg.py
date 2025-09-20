from sympy.core.function import Function
from sympy.concrete.expr_with_limits import Stack
from sympy.functions.special.tensor_functions import Bool
from sympy.sets.contains import Element
from sympy import Range


# https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part
@Function(complex=True, shape=property(lambda self: self.arg.shape))
def BandPart(x, *limits):
    '''
    >>> n = 20
    >>> BandPart[5, 3](Ones(n, n)).this.defun()
    >>> Algebra.eq.then.eq.bool.apply(Eq[-1].this.rhs.doit())     
    >>> BandPart[5, 3, 2](Ones(n, n)).this.defun() #dilated version
    >>> Algebra.eq.then.eq.bool.apply(Eq[-1].this.rhs.doit())
    '''
    
    if len(limits) == 3:
        (num_lower,), (num_upper,), (dilation,) = limits
    else:
        (num_lower,), (num_upper,) = limits
        dilation = 1
    m, n = x.shape
    excludes = num_lower.free_symbols | num_upper.free_symbols
    i = x.generate_var(excludes=excludes, var='i', integer=True)
    excludes.add(i)
    j = x.generate_var(excludes=excludes, var='j', integer=True)
    
    return x * Stack[j:n, i:m](Bool(Element(j - i, Range(-num_lower, num_upper + 1, step=dilation))))

   