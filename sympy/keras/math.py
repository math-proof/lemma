from sympy.core.function import Function

@Function(shape=property(lambda self: self.arg.shape[:-1]), is_finite=True)
def logsumexp(x):
    from sympy.concrete.reduced import ReducedSum
    from sympy.functions.elementary.exponential import Exp, log
    return log(ReducedSum(Exp(x)))