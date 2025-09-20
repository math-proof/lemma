""" A module which handles Matrix Expressions """

from .slice import MatrixSlice
from .blockmatrix import BlockMatrix, BlockDiagMatrix, block_collapse, blockcut
from .cofactor import Cofactors

from .funcmatrix import FunctionMatrix
from .inverse import Inverse
from .matexpr import Identity, MatrixExpr, MatrixSymbol, Zeros, Ones, matrix_symbols, SwapMatrix, AddMatrix, MulMatrix, ShiftMatrix

from .matmul import MatMul
from .matpow import MatPow
from .trace import Trace, trace
from .determinant import Det, det, Determinant
from .minors import Minors

from .transpose import Transpose
from .adjoint import Adjoint
from .hadamard import hadamard_product, HadamardProduct, hadamard_power, HadamardPower
from .diagonal import DiagonalMatrix, DiagonalOf, DiagonalizeVector, diagonalize_vector
from .dotproduct import DotProduct
from .kronecker import kronecker_product, KroneckerProduct, combine_kronecker
from .sets import MatrixSet
