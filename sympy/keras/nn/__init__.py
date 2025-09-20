from sympy.core.function import Function
from sympy.functions.elementary.miscellaneous import Max
from sympy.functions.elementary.exponential import exp
from sympy.concrete.reduced import ReducedSum
from sympy.core.containers import Tuple


class Softmax(Function):
    r"""
    x is a vector
    softmax(x) = exp(x) / Sum(exp(x))
    Sum(softmax(x)) = 1
    """
    is_nonnegative = True
     
    def _eval_is_extended_positive(self):
        return self.arg.is_finite
        
    def _eval_is_zero(self):
        if self.arg.is_finite:
            return False
    
    @classmethod
    def eval(cls, arg):
        ...
 
    def simplify(self, **_):
        return self
 
    def __getitem__(self, indices):
        if (indices := self.simplify_indices(indices)) is None:
            return self

        if len(self.shape) == 1:
            x = self.arg
            return exp(x[indices]) / ReducedSum(exp(x))

        if isinstance(indices, tuple):
            i, *rest = indices
            if isinstance(i, Tuple):
                if len(self.shape) == 2:
                    from sympy import Stack, Basic
                    j = self.generate_var(integer=True, excludes={j for j in indices if isinstance(j, Basic)})
                    self = Stack[j:self.shape[0]](self.func(self.arg[j]))
                    return self[indices]
            else:
                return self.func(self.arg[i])[rest]
        else:
            return self.func(self.arg[indices])
 
    def __iter__(self):
        raise TypeError
 
    def _latex(self, p):
        return r"softmax\left(%s\right)" % p._print(self.arg)
 
    @property
    def T(self):
        from sympy import Transpose
        return Transpose(self)


softmax = Softmax

def __iter__(self):
    raise TypeError

# https://tensorflow.google.cn/api_docs/python/tf/nn/relu?hl=en
@Function(real=True,
          extended_negative=False,
          _eval_is_extended_integer=lambda self: self.arg.is_extended_integer,
          _eval_is_extended_positive=lambda self: self.arg.is_extended_positive,
          _eval_is_finite=lambda self: True if self.is_extended_negative else self.is_finite,
          __iter__=__iter__,
          __getitem__=lambda self, indices: self.func(self.arg[indices], evaluate=False),
          dtype=property(lambda self: self.arg.dtype))
def relu(x):
    '''
    >>> x = Symbol(real=True) 
    >>> relu(x).this.defun()
    '''
    return Max(x, 0)


@Function(extended_real=True,
          extended_positive=True,
          finite=True,
          __iter__=__iter__,
          __getitem__=lambda self, index: self.func(self.arg[index]))
def sigmoid(x):
    return 1 / (1 + exp(-x))

sigmoid.name = 'sigmar'
