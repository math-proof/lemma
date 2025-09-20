"""
This module defines tensors with abstract index notation.

The abstract index notation has been first formalized by Penrose.

Tensor indices are formal objects, with a tensor type; there is no
notion of index range, it is only possible to assign the dimension,
used to trace the Kronecker delta; the dimension can be a Symbol.

The Einstein summation convention is used.
The covariant indices are indicated with a minus sign in front of the index.

For instance the tensor ``t = p(a)*A(b,c)*q(-c)`` has the index ``c``
contracted.

A tensor expression ``t`` can be called; called with its
indices in sorted order it is equal to itself:
in the above example ``t(a, b) == t``;
one can call ``t`` with different indices; ``t(c, d) == p(c)*A(d,a)*q(-a)``.

The contracted indices are dummy indices, internally they have no name,
the indices being represented by a graph-like structure.

Tensors are put in canonical form using ``canon_bp``, which uses
the Butler-Portugal algorithm for canonicalization using the monoterm
symmetries of the tensors.

If there is a (anti)symmetric metric, the indices can be raised and
lowered when the tensor is put in canonical form.
"""

from collections import defaultdict
import operator
import itertools
from sympy import Rational, prod, Integer
from sympy.combinatorics.tensor_can import get_symmetric_group_sgs, \
    bsgs_direct_product, canonicalize, riemann_bsgs
from sympy.core import Basic, Expr, sympify, Add, Mul, S
from sympy.core.compatibility import reduce, SYMPY_INTS, ordered
from sympy.core.containers import Tuple, Dict
from sympy.core.decorators import deprecated
from sympy.core.symbol import Symbol, symbols
from sympy.core.sympify import CantSympify, _sympify, SympifyError
from sympy.core.operations import AssocOp
from sympy.matrices import eye
from sympy.utilities.exceptions import SymPyDeprecationWarning
import warnings
from sympy.logic.boolalg import Boolean, BooleanAtom
from sympy.core.parameters import global_parameters
from sympy.matrices.expressions.matexpr import Ones
from sympy.core.cache import cacheit
from sympy.core.relational import Equal, Unequal, GreaterEqual, LessEqual,\
    Greater, Less


@deprecated(useinstead=".replace_with_arrays", issue=15276, deprecated_since_version="1.4")
def deprecate_data():
    pass


class _IndexStructure(CantSympify):
    """
    This class handles the indices (free and dummy ones). It contains the
    algorithms to manage the dummy indices replacements and contractions of
    free indices under multiplications of tensor expressions, as well as stuff
    related to canonicalization sorting, getting the permutation of the
    expression and so on. It also includes tools to get the ``TensorIndex``
    objects corresponding to the given index structure.
    """

    def __init__(self, free, dum, index_types, indices, canon_bp=False):
        self.free = free
        self.dum = dum
        self.index_types = index_types
        self.indices = indices
        self._ext_rank = len(self.free) + 2*len(self.dum)
        self.dum.sort(key=lambda x: x[0])

    @staticmethod
    def from_indices(*indices):
        """
        Create a new ``_IndexStructure`` object from a list of ``indices``

        ``indices``     ``TensorIndex`` objects, the indices. Contractions are
                        detected upon construction.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, _IndexStructure
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2, m3 = tensor_indices('m0,m1,m2,m3', Lorentz)
        >>> _IndexStructure.from_indices(m0, m1, -m1, m3)
        _IndexStructure([(m0, 0), (m3, 3)], [(1, 2)], [Lorentz, Lorentz, Lorentz, Lorentz])

        In case of many components the same indices have slightly different
        indexes:

        >>> _IndexStructure.from_indices(m0, m1, -m1, m3)
        _IndexStructure([(m0, 0), (m3, 3)], [(1, 2)], [Lorentz, Lorentz, Lorentz, Lorentz])
        """
        free, dum = _IndexStructure._free_dum_from_indices(*indices)
        index_types = [i.tensor_index_type for i in indices]
        indices = _IndexStructure._replace_dummy_names(indices, free, dum)
        return _IndexStructure(free, dum, index_types, indices)

    @staticmethod
    def from_components_free_dum(components, free, dum):
        index_types = []
        for component in components:
            index_types.extend(component.index_types)
        indices = _IndexStructure.generate_indices_from_free_dum_index_types(free, dum, index_types)
        return _IndexStructure(free, dum, index_types, indices)

    @staticmethod
    def _free_dum_from_indices(*indices):
        """
        Convert ``indices`` into ``free``, ``dum`` for single component tensor

        ``free``     list of tuples ``(index, pos, 0)``,
                     where ``pos`` is the position of index in
                     the list of indices formed by the component tensors

        ``dum``      list of tuples ``(pos_contr, pos_cov, 0, 0)``

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, \
            _IndexStructure
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2, m3 = tensor_indices('m0,m1,m2,m3', Lorentz)
        >>> _IndexStructure._free_dum_from_indices(m0, m1, -m1, m3)
        ([(m0, 0), (m3, 3)], [(1, 2)])
        """
        n = len(indices)
        if n == 1:
            return [(indices[0], 0)], []

        # find the positions of the free indices and of the dummy indices
        free = [True]*len(indices)
        index_dict = {}
        dum = []
        for i, index in enumerate(indices):
            name = index._name
            typ = index.tensor_index_type
            contr = index._is_up
            if (name, typ) in index_dict:
                # found a pair of dummy indices
                is_contr, pos = index_dict[(name, typ)]
                # check consistency and update free
                if is_contr:
                    if contr:
                        raise ValueError('two equal contravariant indices in slots %d and %d' %(pos, i))
                    else:
                        free[pos] = False
                        free[i] = False
                else:
                    if contr:
                        free[pos] = False
                        free[i] = False
                    else:
                        raise ValueError('two equal covariant indices in slots %d and %d' %(pos, i))
                if contr:
                    dum.append((i, pos))
                else:
                    dum.append((pos, i))
            else:
                index_dict[(name, typ)] = index._is_up, i

        free = [(index, i) for i, index in enumerate(indices) if free[i]]
        free.sort()
        return free, dum

    def get_indices(self):
        """
        Get a list of indices, creating new tensor indices to complete dummy indices.
        """
        return self.indices[:]

    @staticmethod
    def generate_indices_from_free_dum_index_types(free, dum, index_types):
        indices = [None]*(len(free)+2*len(dum))
        for idx, pos in free:
            indices[pos] = idx

        generate_dummy_name = _IndexStructure._get_generator_for_dummy_indices(free)
        for pos1, pos2 in dum:
            typ1 = index_types[pos1]
            indname = generate_dummy_name(typ1)
            indices[pos1] = TensorIndex(indname, typ1, True)
            indices[pos2] = TensorIndex(indname, typ1, False)

        return _IndexStructure._replace_dummy_names(indices, free, dum)

    @staticmethod
    def _get_generator_for_dummy_indices(free):
        cdt = defaultdict(int)
        # if the free indices have names with dummy_fmt, start with an
        # index higher than those for the dummy indices
        # to avoid name collisions
        for indx, ipos in free:
            if indx._name.split('_')[0] == indx.tensor_index_type.dummy_fmt[:-3]:
                cdt[indx.tensor_index_type] = max(cdt[indx.tensor_index_type], int(indx._name.split('_')[1]) + 1)

        def dummy_fmt_gen(tensor_index_type):
            fmt = tensor_index_type.dummy_fmt
            nd = cdt[tensor_index_type]
            cdt[tensor_index_type] += 1
            return fmt % nd

        return dummy_fmt_gen

    @staticmethod
    def _replace_dummy_names(indices, free, dum):
        dum.sort(key=lambda x: x[0])
        new_indices = [ind for ind in indices]
        assert len(indices) == len(free) + 2*len(dum)
        generate_dummy_name = _IndexStructure._get_generator_for_dummy_indices(free)
        for ipos1, ipos2 in dum:
            typ1 = new_indices[ipos1].tensor_index_type
            indname = generate_dummy_name(typ1)
            new_indices[ipos1] = TensorIndex(indname, typ1, True)
            new_indices[ipos2] = TensorIndex(indname, typ1, False)
        return new_indices

    def get_free_indices(self):
        """
        Get a list of free indices.
        """
        # get sorted indices according to their position:
        free = sorted(self.free, key=lambda x: x[1])
        return [i[0] for i in free]

    def __str__(self):
        return "_IndexStructure({0}, {1}, {2})".format(self.free, self.dum, self.index_types)

    def __repr__(self):
        return self.__str__()

    def _get_sorted_free_indices_for_canon(self):
        sorted_free = self.free[:]
        sorted_free.sort(key=lambda x: x[0])
        return sorted_free

    def _get_sorted_dum_indices_for_canon(self):
        return sorted(self.dum, key=lambda x: x[0])

    def _get_lexicographically_sorted_index_types(self):
        permutation = self.indices_canon_args()[0]
        index_types = [None]*self._ext_rank
        for i, it in enumerate(self.index_types):
            index_types[permutation(i)] = it
        return index_types

    def _get_lexicographically_sorted_indices(self):
        permutation = self.indices_canon_args()[0]
        indices = [None]*self._ext_rank
        for i, it in enumerate(self.indices):
            indices[permutation(i)] = it
        return indices

    def perm2tensor(self, g, is_canon_bp=False):
        """
        Returns a ``_IndexStructure`` instance corresponding to the permutation ``g``

        ``g``  permutation corresponding to the tensor in the representation
        used in canonicalization

        ``is_canon_bp``   if True, then ``g`` is the permutation
        corresponding to the canonical form of the tensor
        """
        sorted_free = [i[0] for i in self._get_sorted_free_indices_for_canon()]
        lex_index_types = self._get_lexicographically_sorted_index_types()
        lex_indices = self._get_lexicographically_sorted_indices()
        nfree = len(sorted_free)
        rank = self._ext_rank
        dum = [[None]*2 for i in range((rank - nfree)//2)]
        free = []

        index_types = [None]*rank
        indices = [None]*rank
        for i in range(rank):
            gi = g[i]
            index_types[i] = lex_index_types[gi]
            indices[i] = lex_indices[gi]
            if gi < nfree:
                ind = sorted_free[gi]
                assert index_types[i] == sorted_free[gi].tensor_index_type
                free.append((ind, i))
            else:
                j = gi - nfree
                idum, cov = divmod(j, 2)
                if cov:
                    dum[idum][1] = i
                else:
                    dum[idum][0] = i
        dum = [tuple(x) for x in dum]

        return _IndexStructure(free, dum, index_types, indices)

    def indices_canon_args(self):
        """
        Returns ``(g, dummies, msym, v)``, the entries of ``canonicalize``

        see ``canonicalize`` in ``tensor_can.py``
        """
        # to be called after sorted_components
        from sympy.combinatorics.permutations import _af_new
        n = self._ext_rank
        g = [None]*n + [n, n+1]

        # ordered indices: first the free indices, ordered by types
        # then the dummy indices, ordered by types and contravariant before
        # covariant
        # g[position in tensor] = position in ordered indices
        for i, (indx, ipos) in enumerate(self._get_sorted_free_indices_for_canon()):
            g[ipos] = i
        pos = len(self.free)
        j = len(self.free)
        dummies = []
        prev = None
        a = []
        msym = []
        for ipos1, ipos2 in self._get_sorted_dum_indices_for_canon():
            g[ipos1] = j
            g[ipos2] = j + 1
            j += 2
            typ = self.index_types[ipos1]
            if typ != prev:
                if a:
                    dummies.append(a)
                a = [pos, pos + 1]
                prev = typ
                msym.append(typ.metric_antisym)
            else:
                a.extend([pos, pos + 1])
            pos += 2
        if a:
            dummies.append(a)

        return _af_new(g), dummies, msym


def components_canon_args(components):
    numtyp = []
    prev = None
    for t in components:
        if t == prev:
            numtyp[-1][1] += 1
        else:
            prev = t
            numtyp.append([prev, 1])
    v = []
    for h, n in numtyp:
        if h._comm == 0 or h._comm == 1:
            comm = h._comm
        else:
            comm = TensorManager.get_comm(h._comm, h._comm)
        v.append((h._symmetry.base, h._symmetry.generators, n, comm))
    return v


class _TensorDataLazyEvaluator(CantSympify):
    """
    EXPERIMENTAL: do not rely on this class, it may change without deprecation
    warnings in future versions of SymPy.

    This object contains the logic to associate components data to a tensor
    expression. Components data are set via the ``.data`` property of tensor
    expressions, is stored inside this class as a mapping between the tensor
    expression and the ``ndarray``.

    Computations are executed lazily: whereas the tensor expressions can have
    contractions, tensor products, and additions, components data are not
    computed until they are accessed by reading the ``.data`` property
    associated to the tensor expression.
    """
    _substitutions_dict = dict()
    _substitutions_dict_tensmul = dict()

    def __getitem__(self, key):
        dat = self._get(key)
        if dat is None:
            return None

        from .array import NDimArray
        if not isinstance(dat, NDimArray):
            return dat

        if dat.rank() == 0:
            return dat[()]
        elif dat.rank() == 1 and len(dat) == 1:
            return dat[0]
        return dat

    def _get(self, key):
        """
        Retrieve ``data`` associated with ``key``.

        This algorithm looks into ``self._substitutions_dict`` for all
        ``TensorHead`` in the ``TensExpr`` (or just ``TensorHead`` if key is a
        TensorHead instance). It reconstructs the components data that the
        tensor expression should have by performing on components data the
        operations that correspond to the abstract tensor operations applied.

        Metric tensor is handled in a different manner: it is pre-computed in
        ``self._substitutions_dict_tensmul``.
        """
        if key in self._substitutions_dict:
            return self._substitutions_dict[key]

        if isinstance(key, TensorHead):
            return None

        if isinstance(key, Tensor):
            # special case to handle metrics. Metric tensors cannot be
            # constructed through contraction by the metric, their
            # components show if they are a matrix or its inverse.
            signature = tuple([i.is_up for i in key.get_indices()])
            srch = (key.component,) + signature
            if srch in self._substitutions_dict_tensmul:
                return self._substitutions_dict_tensmul[srch]
            array_list = [self.data_from_tensor(key)]
            return self.data_contract_dum(array_list, key.dum, key.ext_rank)

        if isinstance(key, TensMul):
            tensmul_args = key.args
            if len(tensmul_args) == 1 and len(tensmul_args[0].components) == 1:
                # special case to handle metrics. Metric tensors cannot be
                # constructed through contraction by the metric, their
                # components show if they are a matrix or its inverse.
                signature = tuple([i.is_up for i in tensmul_args[0].get_indices()])
                srch = (tensmul_args[0].components[0],) + signature
                if srch in self._substitutions_dict_tensmul:
                    return self._substitutions_dict_tensmul[srch]
            #data_list = [self.data_from_tensor(i) for i in tensmul_args if isinstance(i, TensExpr)]
            data_list = [self.data_from_tensor(i) if isinstance(i, Tensor) else i.data for i in tensmul_args if isinstance(i, TensExpr)]
            coeff = prod([i for i in tensmul_args if not isinstance(i, TensExpr)])
            if all([i is None for i in data_list]):
                return None
            if any([i is None for i in data_list]):
                raise ValueError("Mixing tensors with associated components "\
                                 "data with tensors without components data")
            data_result = self.data_contract_dum(data_list, key.dum, key.ext_rank)
            return coeff*data_result

        if isinstance(key, TensAdd):
            data_list = []
            free_args_list = []
            for arg in key.args:
                if isinstance(arg, TensExpr):
                    data_list.append(arg.data)
                    free_args_list.append([x[0] for x in arg.free])
                else:
                    data_list.append(arg)
                    free_args_list.append([])
            if all([i is None for i in data_list]):
                return None
            if any([i is None for i in data_list]):
                raise ValueError("Mixing tensors with associated components "\
                                 "data with tensors without components data")

            sum_list = []
            from .array import permutedims
            for data, free_args in zip(data_list, free_args_list):
                if len(free_args) < 2:
                    sum_list.append(data)
                else:
                    free_args_pos = {y: x for x, y in enumerate(free_args)}
                    axes = [free_args_pos[arg] for arg in key.free_args]
                    sum_list.append(permutedims(data, axes))
            return reduce(lambda x, y: x+y, sum_list)

        return None

    @staticmethod
    def data_contract_dum(ndarray_list, dum, ext_rank):
        from .array import tensorproduct, tensorcontraction, MutableDenseNDimArray
        arrays = list(map(MutableDenseNDimArray, ndarray_list))
        prodarr = tensorproduct(*arrays)
        return tensorcontraction(prodarr, *dum)

    def data_tensorhead_from_tensmul(self, data, tensmul, tensorhead):
        """
        This method is used when assigning components data to a ``TensMul``
        object, it converts components data to a fully contravariant ndarray,
        which is then stored according to the ``TensorHead`` key.
        """
        if data is None:
            return None

        return self._correct_signature_from_indices(
            data,
            tensmul.get_indices(),
            tensmul.free,
            tensmul.dum,
            True)

    def data_from_tensor(self, tensor):
        """
        This method corrects the components data to the right signature
        (covariant/contravariant) using the metric associated with each
        ``TensorIndexType``.
        """
        tensorhead = tensor.component

        if tensorhead.data is None:
            return None

        return self._correct_signature_from_indices(
            tensorhead.data,
            tensor.get_indices(),
            tensor.free,
            tensor.dum)

    def _assign_data_to_tensor_expr(self, key, data):
        if isinstance(key, TensAdd):
            raise ValueError('cannot assign data to TensAdd')
        # here it is assumed that `key` is a `TensMul` instance.
        if len(key.components) != 1:
            raise ValueError('cannot assign data to TensMul with multiple components')
        tensorhead = key.components[0]
        newdata = self.data_tensorhead_from_tensmul(data, key, tensorhead)
        return tensorhead, newdata

    def _check_permutations_on_data(self, tens, data):
        from .array import permutedims

        if isinstance(tens, TensorHead):
            rank = tens.rank
            generators = tens.symmetry.generators
        elif isinstance(tens, Tensor):
            rank = tens.rank
            generators = tens.components[0].symmetry.generators
        elif isinstance(tens, TensorIndexType):
            rank = tens.metric.rank
            generators = tens.metric.symmetry.generators

        # Every generator is a permutation, check that by permuting the array
        # by that permutation, the array will be the same, except for a
        # possible sign change if the permutation admits it.
        for gener in generators:
            sign_change = +1 if (gener(rank) == rank) else -1
            data_swapped = data
            last_data = data
            permute_axes = list(map(gener, list(range(rank))))
            # the order of a permutation is the number of times to get the
            # identity by applying that permutation.
            for i in range(gener.order()-1):
                data_swapped = permutedims(data_swapped, permute_axes)
                # if any value in the difference array is non-zero, raise an error:
                if any(last_data - sign_change*data_swapped):
                    raise ValueError("Component data symmetry structure error")
                last_data = data_swapped

    def __setitem__(self, key, value):
        """
        Set the components data of a tensor object/expression.

        Components data are transformed to the all-contravariant form and stored
        with the corresponding ``TensorHead`` object. If a ``TensorHead`` object
        cannot be uniquely identified, it will raise an error.
        """
        data = _TensorDataLazyEvaluator.parse_data(value)
        self._check_permutations_on_data(key, data)

        # TensorHead and TensorIndexType can be assigned data directly, while
        # TensMul must first convert data to a fully contravariant form, and
        # assign it to its corresponding TensorHead single component.
        if not isinstance(key, (TensorHead, TensorIndexType)):
            key, data = self._assign_data_to_tensor_expr(key, data)

        if isinstance(key, TensorHead):
            for dim, indextype in zip(data.shape, key.index_types):
                if indextype.data is None:
                    raise ValueError("index type {} has no components data"\
                    " associated (needed to raise/lower index)".format(indextype))
                if indextype.dim is None:
                    continue
                if dim != indextype.dim:
                    raise ValueError("wrong dimension of ndarray")
        self._substitutions_dict[key] = data

    def __delitem__(self, key):
        del self._substitutions_dict[key]

    def __contains__(self, key):
        return key in self._substitutions_dict

    def add_metric_data(self, metric, data):
        """
        Assign data to the ``metric`` tensor. The metric tensor behaves in an
        anomalous way when raising and lowering indices.

        A fully covariant metric is the inverse transpose of the fully
        contravariant metric (it is meant matrix inverse). If the metric is
        symmetric, the transpose is not necessary and mixed
        covariant/contravariant metrics are Kronecker deltas.
        """
        # hard assignment, data should not be added to `TensorHead` for metric:
        # the problem with `TensorHead` is that the metric is anomalous, i.e.
        # raising and lowering the index means considering the metric or its
        # inverse, this is not the case for other tensors.
        self._substitutions_dict_tensmul[metric, True, True] = data
        inverse_transpose = self.inverse_transpose_matrix(data)
        # in symmetric spaces, the traspose is the same as the original matrix,
        # the full covariant metric tensor is the inverse transpose, so this
        # code will be able to handle non-symmetric metrics.
        self._substitutions_dict_tensmul[metric, False, False] = inverse_transpose
        # now mixed cases, these are identical to the unit matrix if the metric
        # is symmetric.
        m = data.tomatrix()
        invt = inverse_transpose.tomatrix()
        self._substitutions_dict_tensmul[metric, True, False] = m * invt
        self._substitutions_dict_tensmul[metric, False, True] = invt * m

    @staticmethod
    def _flip_index_by_metric(data, metric, pos):
        from .array import tensorproduct, tensorcontraction

        mdim = metric.rank()
        ddim = data.rank()

        if pos == 0:
            data = tensorcontraction(
                tensorproduct(
                    metric,
                    data
                ),
                (1, mdim+pos)
            )
        else:
            data = tensorcontraction(
                tensorproduct(
                    data,
                    metric
                ),
                (pos, ddim)
            )
        return data

    @staticmethod
    def inverse_matrix(ndarray):
        m = ndarray.tomatrix().inv()
        return _TensorDataLazyEvaluator.parse_data(m)

    @staticmethod
    def inverse_transpose_matrix(ndarray):
        m = ndarray.tomatrix().inv().T
        return _TensorDataLazyEvaluator.parse_data(m)

    @staticmethod
    def _correct_signature_from_indices(data, indices, free, dum, inverse=False):
        """
        Utility function to correct the values inside the components data
        ndarray according to whether indices are covariant or contravariant.

        It uses the metric matrix to lower values of covariant indices.
        """
        # change the ndarray values according covariantness/contravariantness of the indices
        # use the metric
        for i, indx in enumerate(indices):
            if not indx.is_up and not inverse:
                data = _TensorDataLazyEvaluator._flip_index_by_metric(data, indx.tensor_index_type.data, i)
            elif not indx.is_up and inverse:
                data = _TensorDataLazyEvaluator._flip_index_by_metric(
                    data,
                    _TensorDataLazyEvaluator.inverse_matrix(indx.tensor_index_type.data),
                    i
                )
        return data

    @staticmethod
    def _sort_data_axes(old, new):
        from .array import permutedims

        new_data = old.data.copy()

        old_free = [i[0] for i in old.free]
        new_free = [i[0] for i in new.free]

        for i in range(len(new_free)):
            for j in range(i, len(old_free)):
                if old_free[j] == new_free[i]:
                    old_free[i], old_free[j] = old_free[j], old_free[i]
                    new_data = permutedims(new_data, (i, j))
                    break
        return new_data

    @staticmethod
    def add_rearrange_tensmul_parts(new_tensmul, old_tensmul):
        def sorted_compo():
            return _TensorDataLazyEvaluator._sort_data_axes(old_tensmul, new_tensmul)

        _TensorDataLazyEvaluator._substitutions_dict[new_tensmul] = sorted_compo()

    @staticmethod
    def parse_data(data):
        """
        Transform ``data`` to array. The parameter ``data`` may
        contain data in various formats, e.g. nested lists, sympy ``Matrix``,
        and so on.

        Examples
        ========

        >>> from sympy.tensor.tensor import _TensorDataLazyEvaluator
        >>> _TensorDataLazyEvaluator.parse_data([1, 3, -6, 12])
        [1, 3, -6, 12]

        >>> _TensorDataLazyEvaluator.parse_data([[1, 2], [4, 7]])
        [[1, 2], [4, 7]]
        """
        from .array import MutableDenseNDimArray

        if not isinstance(data, MutableDenseNDimArray):
            if len(data) == 2 and hasattr(data[0], '__call__'):
                data = MutableDenseNDimArray(data[0], data[1])
            else:
                data = MutableDenseNDimArray(data)
        return data

_tensor_data_substitution_dict = _TensorDataLazyEvaluator()


class _TensorManager(object):
    """
    Class to manage tensor properties.

    Notes
    =====

    Tensors belong to tensor commutation groups; each group has a label
    ``comm``; there are predefined labels:

    ``0``   tensors commuting with any other tensor

    ``1``   tensors anticommuting among themselves

    ``2``   tensors not commuting, apart with those with ``comm=0``

    Other groups can be defined using ``set_comm``; tensors in those
    groups commute with those with ``comm=0``; by default they
    do not commute with any other group.
    """
    def __init__(self):
        self._comm_init()

    def _comm_init(self):
        self._comm = [{} for i in range(3)]
        for i in range(3):
            self._comm[0][i] = 0
            self._comm[i][0] = 0
        self._comm[1][1] = 1
        self._comm[2][1] = None
        self._comm[1][2] = None
        self._comm_symbols2i = {0:0, 1:1, 2:2}
        self._comm_i2symbol = {0:0, 1:1, 2:2}

    @property
    def comm(self):
        return self._comm

    def comm_symbols2i(self, i):
        """
        get the commutation group number corresponding to ``i``

        ``i`` can be a symbol or a number or a string

        If ``i`` is not already defined its commutation group number
        is set.
        """
        if i not in self._comm_symbols2i:
            n = len(self._comm)
            self._comm.append({})
            self._comm[n][0] = 0
            self._comm[0][n] = 0
            self._comm_symbols2i[i] = n
            self._comm_i2symbol[n] = i
            return n
        return self._comm_symbols2i[i]

    def comm_i2symbol(self, i):
        """
        Returns the symbol corresponding to the commutation group number.
        """
        return self._comm_i2symbol[i]

    def set_comm(self, i, j, c):
        """
        set the commutation parameter ``c`` for commutation groups ``i, j``

        Parameters
        ==========

        i, j : symbols representing commutation groups

        c  :  group commutation number

        Notes
        =====

        ``i, j`` can be symbols, strings or numbers,
        apart from ``0, 1`` and ``2`` which are reserved respectively
        for commuting, anticommuting tensors and tensors not commuting
        with any other group apart with the commuting tensors.
        For the remaining cases, use this method to set the commutation rules;
        by default ``c=None``.

        The group commutation number ``c`` is assigned in correspondence
        to the group commutation symbols; it can be

        0        commuting

        1        anticommuting

        None     no commutation property

        Examples
        ========

        ``G`` and ``GH`` do not commute with themselves and commute with
        each other; A is commuting.

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead, TensorManager
        >>> Lorentz = TensorIndexType('Lorentz')
        >>> i0,i1,i2,i3,i4 = tensor_indices('i0:5', Lorentz)
        >>> A = tensorhead('A', [Lorentz], [[1]])
        >>> G = tensorhead('G', [Lorentz], [[1]], 'Gcomm')
        >>> GH = tensorhead('GH', [Lorentz], [[1]], 'GHcomm')
        >>> TensorManager.set_comm('Gcomm', 'GHcomm', 0)
        >>> (GH(i1)*G(i0)).canon_bp()
        G(i0)*GH(i1)
        >>> (G(i1)*G(i0)).canon_bp()
        G(i1)*G(i0)
        >>> (G(i1)*A(i0)).canon_bp()
        A(i0)*G(i1)
        """
        if c not in (0, 1, None):
            raise ValueError('`c` can assume only the values 0, 1 or None')

        if i not in self._comm_symbols2i:
            n = len(self._comm)
            self._comm.append({})
            self._comm[n][0] = 0
            self._comm[0][n] = 0
            self._comm_symbols2i[i] = n
            self._comm_i2symbol[n] = i
        if j not in self._comm_symbols2i:
            n = len(self._comm)
            self._comm.append({})
            self._comm[0][n] = 0
            self._comm[n][0] = 0
            self._comm_symbols2i[j] = n
            self._comm_i2symbol[n] = j
        ni = self._comm_symbols2i[i]
        nj = self._comm_symbols2i[j]
        self._comm[ni][nj] = c
        self._comm[nj][ni] = c

    def set_comms(self, *args):
        """
        set the commutation group numbers ``c`` for symbols ``i, j``

        Parameters
        ==========

        args : sequence of ``(i, j, c)``
        """
        for i, j, c in args:
            self.set_comm(i, j, c)

    def get_comm(self, i, j):
        """
        Return the commutation parameter for commutation group numbers ``i, j``

        see ``_TensorManager.set_comm``
        """
        return self._comm[i].get(j, 0 if i == 0 or j == 0 else None)

    def clear(self):
        """
        Clear the TensorManager.
        """
        self._comm_init()


TensorManager = _TensorManager()


class TensorIndexType(Basic):
    """
    A TensorIndexType is characterized by its name and its metric.

    Parameters
    ==========

    name : name of the tensor type

    metric : metric symmetry or metric object or ``None``


    dim : dimension, it can be a symbol or an integer or ``None``

    eps_dim : dimension of the epsilon tensor

    dummy_fmt : name of the head of dummy indices

    Attributes
    ==========

    ``name``
    ``metric_name`` : it is 'metric' or metric.name
    ``metric_antisym``
    ``metric`` : the metric tensor
    ``delta`` : ``Kronecker delta``
    ``epsilon`` : the ``Levi-Civita epsilon`` tensor
    ``dim``
    ``eps_dim``
    ``dummy_fmt``
    ``data`` : a property to add ``ndarray`` values, to work in a specified basis.

    Notes
    =====

    The ``metric`` parameter can be:
    ``metric = False`` symmetric metric (in Riemannian geometry)

    ``metric = True`` antisymmetric metric (for spinor calculus)

    ``metric = None``  there is no metric

    ``metric`` can be an object having ``name`` and ``antisym`` attributes.


    If there is a metric the metric is used to raise and lower indices.

    In the case of antisymmetric metric, the following raising and
    lowering conventions will be adopted:

    ``psi(a) = g(a, b)*psi(-b); chi(-a) = chi(b)*g(-b, -a)``

    ``g(-a, b) = delta(-a, b); g(b, -a) = -delta(a, -b)``

    where ``delta(-a, b) = delta(b, -a)`` is the ``Kronecker delta``
    (see ``TensorIndex`` for the conventions on indices).

    If there is no metric it is not possible to raise or lower indices;
    e.g. the index of the defining representation of ``SU(N)``
    is 'covariant' and the conjugate representation is
    'contravariant'; for ``N > 2`` they are linearly independent.

    ``eps_dim`` is by default equal to ``dim``, if the latter is an integer;
    else it can be assigned (for use in naive dimensional regularization);
    if ``eps_dim`` is not an integer ``epsilon`` is ``None``.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> Lorentz.metric
    metric(Lorentz,Lorentz)
    """

    def __new__(cls, name, metric=False, dim=None, eps_dim=None,
                dummy_fmt=None):

        if isinstance(name, str):
            name = Symbol(name)
        obj = Basic.__new__(cls, name, S.One if metric else S.Zero)
        obj._name = str(name)
        if not dummy_fmt:
            obj._dummy_fmt = '%s_%%d' % obj.name
        else:
            obj._dummy_fmt = '%s_%%d' % dummy_fmt
        if metric is None:
            obj.metric_antisym = None
            obj.metric = None
        else:
            if metric in (True, False, 0, 1):
                metric_name = 'metric'
                obj.metric_antisym = metric
            else:
                metric_name = metric.name
                obj.metric_antisym = metric.antisym
            sym2 = TensorSymmetry(get_symmetric_group_sgs(2, obj.metric_antisym))
            S2 = TensorType([obj]*2, sym2)
            obj.metric = S2(metric_name)

        obj._dim = dim
        obj._delta = obj.get_kronecker_delta()
        obj._eps_dim = eps_dim if eps_dim else dim
        obj._epsilon = obj.get_epsilon()
        obj._autogenerated = []
        return obj

    @property
    @deprecated(useinstead="TensorIndex", issue=12857, deprecated_since_version="1.1")
    def auto_right(self):
        if not hasattr(self, '_auto_right'):
            self._auto_right = TensorIndex("auto_right", self)
        return self._auto_right

    @property
    @deprecated(useinstead="TensorIndex", issue=12857, deprecated_since_version="1.1")
    def auto_left(self):
        if not hasattr(self, '_auto_left'):
            self._auto_left = TensorIndex("auto_left", self)
        return self._auto_left

    @property
    @deprecated(useinstead="TensorIndex", issue=12857, deprecated_since_version="1.1")
    def auto_index(self):
        if not hasattr(self, '_auto_index'):
            self._auto_index = TensorIndex("auto_index", self)
        return self._auto_index

    @property
    def data(self):
        deprecate_data()
        return _tensor_data_substitution_dict[self]

    @data.setter
    def data(self, data):
        deprecate_data()
        # This assignment is a bit controversial, should metric components be assigned
        # to the metric only or also to the TensorIndexType object? The advantage here
        # is the ability to assign a 1D array and transform it to a 2D diagonal array.
        from .array import MutableDenseNDimArray

        data = _TensorDataLazyEvaluator.parse_data(data)
        if data.rank() > 2:
            raise ValueError("data have to be of rank 1 (diagonal metric) or 2.")
        if data.rank() == 1:
            if self.dim is not None:
                nda_dim = data.shape[0]
                if nda_dim != self.dim:
                    raise ValueError("Dimension mismatch")

            dim = data.shape[0]
            newndarray = MutableDenseNDimArray.zeros(dim, dim)
            for i, val in enumerate(data):
                newndarray[i, i] = val
            data = newndarray
        dim1, dim2 = data.shape
        if dim1 != dim2:
            raise ValueError("Non-square matrix tensor.")
        if self.dim is not None:
            if self.dim != dim1:
                raise ValueError("Dimension mismatch")
        _tensor_data_substitution_dict[self] = data
        _tensor_data_substitution_dict.add_metric_data(self.metric, data)
        delta = self.get_kronecker_delta()
        i1 = TensorIndex('i1', self)
        i2 = TensorIndex('i2', self)
        delta(i1, -i2).data = _TensorDataLazyEvaluator.parse_data(eye(dim1))

    @data.deleter
    def data(self):
        deprecate_data()
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]
        if self.metric in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self.metric]

    def _get_matrix_fmt(self, number):
        return ("m" + self.dummy_fmt) % (number)

    @property
    def name(self):
        return self._name

    @property
    def dim(self):
        return self._dim

    @property
    def delta(self):
        return self._delta

    @property
    def eps_dim(self):
        return self._eps_dim

    @property
    def epsilon(self):
        return self._epsilon

    @property
    def dummy_fmt(self):
        return self._dummy_fmt

    def get_kronecker_delta(self):
        sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        S2 = TensorType([self]*2, sym2)
        delta = S2('KD')
        return delta

    def get_epsilon(self):
        if not isinstance(self._eps_dim, (SYMPY_INTS, Integer)):
            return None
        sym = TensorSymmetry(get_symmetric_group_sgs(self._eps_dim, 1))
        Sdim = TensorType([self]*self._eps_dim, sym)
        epsilon = Sdim('Eps')
        return epsilon

    def __lt__(self, other):
        return self.name < other.name

    def __str__(self):
        return self.name

    __repr__ = __str__

    def _components_data_full_destroy(self):
        """
        EXPERIMENTAL: do not rely on this API method.

        This destroys components data associated to the ``TensorIndexType``, if
        any, specifically:

        * metric tensor data
        * Kronecker tensor data
        """
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]

        def delete_tensmul_data(key):
            if key in _tensor_data_substitution_dict._substitutions_dict_tensmul:
                del _tensor_data_substitution_dict._substitutions_dict_tensmul[key]

        # delete metric data:
        delete_tensmul_data((self.metric, True, True))
        delete_tensmul_data((self.metric, True, False))
        delete_tensmul_data((self.metric, False, True))
        delete_tensmul_data((self.metric, False, False))

        # delete delta tensor data:
        delta = self.get_kronecker_delta()
        if delta in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[delta]


class TensorIndex(Basic):
    """
    Represents an abstract tensor index.

    Parameters
    ==========

    name : name of the index, or ``True`` if you want it to be automatically assigned
    tensortype : ``TensorIndexType`` of the index
    is_up :  flag for contravariant index

    Attributes
    ==========

    ``name``
    ``tensortype``
    ``is_up``

    Notes
    =====

    Tensor indices are contracted with the Einstein summation convention.

    An index can be in contravariant or in covariant form; in the latter
    case it is represented prepending a ``-`` to the index name.

    Dummy indices have a name with head given by ``tensortype._dummy_fmt``


    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, TensorIndex, TensorSymmetry, TensorType, get_symmetric_group_sgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> i = TensorIndex('i', Lorentz); i
    i
    >>> sym1 = TensorSymmetry(*get_symmetric_group_sgs(1))
    >>> S1 = TensorType([Lorentz], sym1)
    >>> A, B = S1('A,B')
    >>> A(i)*B(-i)
    A(L_0)*B(-L_0)

    If you want the index name to be automatically assigned, just put ``True``
    in the ``name`` field, it will be generated using the reserved character
    ``_`` in front of its name, in order to avoid conflicts with possible
    existing indices:

    >>> i0 = TensorIndex(True, Lorentz)
    >>> i0
    _i0
    >>> i1 = TensorIndex(True, Lorentz)
    >>> i1
    _i1
    >>> A(i0)*B(-i1)
    A(_i0)*B(-_i1)
    >>> A(i0)*B(-i0)
    A(L_0)*B(-L_0)
    """
    def __new__(cls, name, tensortype, is_up=True):
        if isinstance(name, str):
            name_symbol = Symbol(name)
        elif isinstance(name, Symbol):
            name_symbol = name
        elif name is True:
            name = "_i{0}".format(len(tensortype._autogenerated))
            name_symbol = Symbol(name)
            tensortype._autogenerated.append(name_symbol)
        else:
            raise ValueError("invalid name")

        is_up = sympify(is_up)
        obj = Basic.__new__(cls, name_symbol, tensortype, is_up)
        obj._name = str(name)
        obj._tensor_index_type = tensortype
        obj._is_up = is_up
        return obj

    @property
    def name(self):
        return self._name

    @property
    @deprecated(useinstead="tensor_index_type", issue=12857, deprecated_since_version="1.1")
    def tensortype(self):
        return self.tensor_index_type

    @property
    def tensor_index_type(self):
        return self._tensor_index_type

    @property
    def is_up(self):
        return self._is_up

    def _print(self):
        s = self._name
        if not self._is_up:
            s = '-%s' % s
        return s

    def __lt__(self, other):
        return (self.tensor_index_type, self._name) < (other.tensor_index_type, other._name)

    def __neg__(self):
        t1 = TensorIndex(self.name, self.tensor_index_type,
                (not self.is_up))
        return t1


def tensor_indices(s, typ):
    """
    Returns list of tensor indices given their names and their types

    Parameters
    ==========

    s : string of comma separated names of indices

    typ : ``TensorIndexType`` of the indices

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
    """
    if isinstance(s, str):
        a = [x.name for x in symbols(s, seq=True)]
    else:
        raise ValueError('expecting a string')

    tilist = [TensorIndex(i, typ) for i in a]
    if len(tilist) == 1:
        return tilist[0]
    return tilist


class TensorSymmetry(Basic):
    """
    Monoterm symmetry of a tensor

    Parameters
    ==========

    bsgs : tuple ``(base, sgs)`` BSGS of the symmetry of the tensor

    Attributes
    ==========

    ``base`` : base of the BSGS
    ``generators`` : generators of the BSGS
    ``rank`` : rank of the tensor

    Notes
    =====

    A tensor can have an arbitrary monoterm symmetry provided by its BSGS.
    Multiterm symmetries, like the cyclic symmetry of the Riemann tensor,
    are not covered.

    See Also
    ========

    sympy.combinatorics.tensor_can.get_symmetric_group_sgs

    Examples
    ========

    Define a symmetric tensor

    >>> from sympy.tensor.tensor import TensorIndexType, TensorSymmetry, TensorType, get_symmetric_group_sgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')
    """
    def __new__(cls, *args, **kw_args):
        if len(args) == 1:
            base, generators = args[0]
        elif len(args) == 2:
            base, generators = args
        else:
            raise TypeError("bsgs required, either two separate parameters or one tuple")

        if not isinstance(base, Tuple):
            base = Tuple(*base)
        if not isinstance(generators, Tuple):
            generators = Tuple(*generators)
        obj = Basic.__new__(cls, base, generators, **kw_args)
        return obj

    @property
    def base(self):
        return self.args[0]

    @property
    def generators(self):
        return self.args[1]

    @property
    def rank(self):
        return self.args[1][0].size - 2


def tensorsymmetry(*args):
    """
    Return a ``TensorSymmetry`` object.

    One can represent a tensor with any monoterm slot symmetry group
    using a BSGS.

    ``args`` can be a BSGS
    ``args[0]``    base
    ``args[1]``    sgs

    Usually tensors are in (direct products of) representations
    of the symmetric group;
    ``args`` can be a list of lists representing the shapes of Young tableaux

    Notes
    =====

    For instance:
    ``[[1]]``       vector
    ``[[1]*n]``     symmetric tensor of rank ``n``
    ``[[n]]``       antisymmetric tensor of rank ``n``
    ``[[2, 2]]``    monoterm slot symmetry of the Riemann tensor
    ``[[1],[1]]``   vector*vector
    ``[[2],[1],[1]`` (antisymmetric tensor)*vector*vector

    Notice that with the shape ``[2, 2]`` we associate only the monoterm
    symmetries of the Riemann tensor; this is an abuse of notation,
    since the shape ``[2, 2]`` corresponds usually to the irreducible
    representation characterized by the monoterm symmetries and by the
    cyclic symmetry.

    Examples
    ========

    Symmetric tensor using a Young tableau

    >>> from sympy.tensor.tensor import TensorIndexType, TensorType, tensorsymmetry
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> sym2 = tensorsymmetry([1, 1])
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')

    Symmetric tensor using a ``BSGS`` (base, strong generator set)

    >>> from sympy.tensor.tensor import get_symmetric_group_sgs
    >>> sym2 = tensorsymmetry(*get_symmetric_group_sgs(2))
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')
    """
    from sympy.combinatorics import Permutation

    def tableau2bsgs(a):
        if len(a) == 1:
            # antisymmetric vector
            n = a[0]
            bsgs = get_symmetric_group_sgs(n, 1)
        else:
            if all(x == 1 for x in a):
                # symmetric vector
                n = len(a)
                bsgs = get_symmetric_group_sgs(n)
            elif a == [2, 2]:
                bsgs = riemann_bsgs
            else:
                raise NotImplementedError
        return bsgs

    if not args:
        return TensorSymmetry(Tuple(), Tuple(Permutation(1)))

    if len(args) == 2 and isinstance(args[1][0], Permutation):
        return TensorSymmetry(args)
    base, sgs = tableau2bsgs(args[0])
    for a in args[1:]:
        basex, sgsx = tableau2bsgs(a)
        base, sgs = bsgs_direct_product(base, sgs, basex, sgsx)
    return TensorSymmetry(Tuple(base, sgs))


class TensorType(Basic):
    """
    Class of tensor types.

    Parameters
    ==========

    index_types : list of ``TensorIndexType`` of the tensor indices
    symmetry : ``TensorSymmetry`` of the tensor

    Attributes
    ==========

    ``index_types``
    ``symmetry``
    ``types`` : list of ``TensorIndexType`` without repetitions

    Examples
    ========

    Define a symmetric tensor

    >>> from sympy.tensor.tensor import TensorIndexType, tensorsymmetry, TensorType
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> sym2 = tensorsymmetry([1, 1])
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')
    """
    is_commutative = False

    def __new__(cls, index_types, symmetry, **kw_args):
        assert symmetry.rank == len(index_types)
        obj = Basic.__new__(cls, Tuple(*index_types), symmetry, **kw_args)
        return obj

    @property
    def index_types(self):
        return self.args[0]

    @property
    def symmetry(self):
        return self.args[1]

    @property
    def types(self):
        return sorted(set(self.index_types), key=lambda x: x.name)

    def __str__(self):
        return 'TensorType(%s)' % ([str(x) for x in self.index_types])

    def __call__(self, s, comm=0):
        """
        Return a TensorHead object or a list of TensorHead objects.

        ``s``  name or string of names

        ``comm``: commutation group number
        see ``_TensorManager.set_comm``

        Examples
        ========

        Define symmetric tensors ``V``, ``W`` and ``G``, respectively
        commuting, anticommuting and with no commutation symmetry

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorsymmetry, TensorType, canon_bp
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b = tensor_indices('a,b', Lorentz)
        >>> sym2 = tensorsymmetry([1]*2)
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> V = S2('V')
        >>> W = S2('W', 1)
        >>> G = S2('G', 2)
        >>> canon_bp(V(a, b)*V(-b, -a))
        V(L_0, L_1)*V(-L_0, -L_1)
        >>> canon_bp(W(a, b)*W(-b, -a))
        0
        """
        if isinstance(s, str):
            names = [x.name for x in symbols(s, seq=True)]
        else:
            raise ValueError('expecting a string')
        if len(names) == 1:
            return TensorHead(names[0], self, comm)
        else:
            return [TensorHead(name, self, comm) for name in names]


def tensorhead(name, typ, sym=None, comm=0):
    """
    Function generating tensorhead(s).

    Parameters
    ==========

    name : name or sequence of names (as in ``symbol``)

    typ :  index types

    sym :  same as ``*args`` in ``tensorsymmetry``

    comm : commutation group number
    see ``_TensorManager.set_comm``


    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b = tensor_indices('a,b', Lorentz)
    >>> A = tensorhead('A', [Lorentz]*2, [[1]*2])
    >>> A(a, -b)
    A(a, -b)

    If no symmetry parameter is provided, assume there are not index
    symmetries:

    >>> B = tensorhead('B', [Lorentz, Lorentz])
    >>> B(a, -b)
    B(a, -b)

    """
    if sym is None:
        sym = [[1] for i in range(len(typ))]
    sym = tensorsymmetry(*sym)
    S = TensorType(typ, sym)
    th = S(name, comm)
    return th


class TensorHead(Basic):
    r"""
    Tensor head of the tensor

    Parameters
    ==========

    name : name of the tensor

    typ : list of TensorIndexType

    comm : commutation group number

    Attributes
    ==========

    ``name``
    ``index_types``
    ``rank``
    ``types``  :  equal to ``typ.types``
    ``symmetry`` : equal to ``typ.symmetry``
    ``comm`` : commutation group

    Notes
    =====

    A ``TensorHead`` belongs to a commutation group, defined by a
    symbol on number ``comm`` (see ``_TensorManager.set_comm``);
    tensors in a commutation group have the same commutation properties;
    by default ``comm`` is ``0``, the group of the commuting tensors.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensorhead, TensorType
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> A = tensorhead('A', [Lorentz, Lorentz], [[1],[1]])

    Examples with ndarray values, the components data assigned to the
    ``TensorHead`` object are assumed to be in a fully-contravariant
    representation. In case it is necessary to assign components data which
    represents the values of a non-fully covariant tensor, see the other
    examples.

    >>> from sympy.tensor.tensor import tensor_indices, tensorhead
    >>> from sympy import diag
    >>> i0, i1 = tensor_indices('i0:2', Lorentz)

    Specify a replacement dictionary to keep track of the arrays to use for
    replacements in the tensorial expression. The ``TensorIndexType`` is
    associated to the metric used for contractions (in fully covariant form):

    >>> repl = {Lorentz: diag(1, -1, -1, -1)}

    Let's see some examples of working with components with the electromagnetic
    tensor:

    >>> from sympy import symbols
    >>> Ex, Ey, Ez, Bx, By, Bz = symbols('E_x E_y E_z B_x B_y B_z')
    >>> c = symbols('c', positive=True)

    Let's define `F`, an antisymmetric tensor, we have to assign an
    antisymmetric matrix to it, because `[[2]]` stands for the Young tableau
    representation of an antisymmetric set of two elements:

    >>> F = tensorhead('F', [Lorentz, Lorentz], [[2]])

    Let's update the dictionary to contain the matrix to use in the
    replacements:

    >>> repl.update({F(-i0, -i1): [
    ... [0, Ex/c, Ey/c, Ez/c],
    ... [-Ex/c, 0, -Bz, By],
    ... [-Ey/c, Bz, 0, -Bx],
    ... [-Ez/c, -By, Bx, 0]]})

    Now it is possible to retrieve the contravariant form of the Electromagnetic
    tensor:

    >>> F(i0, i1).replace_with_arrays(repl, [i0, i1])
    [[0, -E_x/c, -E_y/c, -E_z/c], [E_x/c, 0, -B_z, B_y], [E_y/c, B_z, 0, -B_x], [E_z/c, -B_y, B_x, 0]]

    and the mixed contravariant-covariant form:

    >>> F(i0, -i1).replace_with_arrays(repl, [i0, -i1])
    [[0, E_x/c, E_y/c, E_z/c], [E_x/c, 0, B_z, -B_y], [E_y/c, -B_z, 0, B_x], [E_z/c, B_y, -B_x, 0]]

    Energy-momentum of a particle may be represented as:

    >>> from sympy import symbols
    >>> P = tensorhead('P', [Lorentz], [[1]])
    >>> E, px, py, pz = symbols('E p_x p_y p_z', positive=True)
    >>> repl.update({P(i0): [E, px, py, pz]})

    The contravariant and covariant components are, respectively:

    >>> P(i0).replace_with_arrays(repl, [i0])
    [E, p_x, p_y, p_z]
    >>> P(-i0).replace_with_arrays(repl, [-i0])
    [E, -p_x, -p_y, -p_z]

    The contraction of a 1-index tensor by itself:

    >>> expr = P(i0)*P(-i0)
    >>> expr.replace_with_arrays(repl, [])
    E**2 - p_x**2 - p_y**2 - p_z**2
    """
    is_commutative = False

    def __new__(cls, name, typ, comm=0, **kw_args):
        if isinstance(name, str):
            name_symbol = Symbol(name)
        elif isinstance(name, Symbol):
            name_symbol = name
        else:
            raise ValueError("invalid name")

        comm2i = TensorManager.comm_symbols2i(comm)

        obj = Basic.__new__(cls, name_symbol, typ, **kw_args)

        obj._name = obj.args[0].name
        obj._rank = len(obj.index_types)
        obj._symmetry = typ.symmetry
        obj._comm = comm2i
        return obj

    @property
    def name(self):
        return self._name

    @property
    def rank(self):
        return self._rank

    @property
    def symmetry(self):
        return self._symmetry

    @property
    def typ(self):
        return self.args[1]

    @property
    def comm(self):
        return self._comm

    @property
    def types(self):
        return self.args[1].types[:]

    @property
    def index_types(self):
        return self.args[1].index_types[:]

    def __lt__(self, other):
        return (self.name, self.index_types) < (other.name, other.index_types)

    def commutes_with(self, other):
        """
        Returns ``0`` if ``self`` and ``other`` commute, ``1`` if they anticommute.

        Returns ``None`` if ``self`` and ``other`` neither commute nor anticommute.
        """
        r = TensorManager.get_comm(self._comm, other._comm)
        return r

    def _print(self):
        return '%s(%s)' %(self.name, ','.join([str(x) for x in self.index_types]))

    def __call__(self, *indices, **kw_args):
        """
        Returns a tensor with indices.

        There is a special behavior in case of indices denoted by ``True``,
        they are considered auto-matrix indices, their slots are automatically
        filled, and confer to the tensor the behavior of a matrix or vector
        upon multiplication with another tensor containing auto-matrix indices
        of the same ``TensorIndexType``. This means indices get summed over the
        same way as in matrix multiplication. For matrix behavior, define two
        auto-matrix indices, for vector behavior define just one.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b = tensor_indices('a,b', Lorentz)
        >>> A = tensorhead('A', [Lorentz]*2, [[1]*2])
        >>> t = A(a, -b)
        >>> t
        A(a, -b)

        """
        tensor = Tensor(self, indices, **kw_args)
        return tensor.doit()

    def __pow__(self, other):
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
            if self.data is None:
                raise ValueError("No power on abstract tensors.")
        deprecate_data()
        from .array import tensorproduct, tensorcontraction
        metrics = [_.data for _ in self.args[1].args[0]]

        marray = self.data
        marraydim = marray.rank()
        for metric in metrics:
            marray = tensorproduct(marray, metric, marray)
            marray = tensorcontraction(marray, (0, marraydim), (marraydim+1, marraydim+2))

        return marray ** (Rational(1, 2) * other)

    @property
    def data(self):
        deprecate_data()
        return _tensor_data_substitution_dict[self]

    @data.setter
    def data(self, data):
        deprecate_data()
        _tensor_data_substitution_dict[self] = data

    @data.deleter
    def data(self):
        deprecate_data()
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]

    def __iter__(self):
        deprecate_data()
        return self.data.__iter__()

    def _components_data_full_destroy(self):
        """
        EXPERIMENTAL: do not rely on this API method.

        Destroy components data associated to the ``TensorHead`` object, this
        checks for attached components data, and destroys components data too.
        """
        # do not garbage collect Kronecker tensor (it should be done by
        # ``TensorIndexType`` garbage collection)
        if self.name == "KD":
            return

        # the data attached to a tensor must be deleted only by the TensorHead
        # destructor. If the TensorHead is deleted, it means that there are no
        # more instances of that tensor anywhere.
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]


def _get_argtree_pos(expr, pos):
    for p in pos:
        expr = expr.args[p]
    return expr


class TensExpr(Expr):
    """
    Abstract base class for tensor expressions

    Notes
    =====

    A tensor expression is an expression formed by tensors;
    currently the sums of tensors are distributed.

    A ``TensExpr`` can be a ``TensAdd`` or a ``TensMul``.

    ``TensAdd`` objects are put in canonical form using the Butler-Portugal
    algorithm for canonicalization under monoterm symmetries.

    ``TensMul`` objects are formed by products of component tensors,
    and include a coefficient, which is a SymPy expression.


    In the internal representation contracted indices are represented
    by ``(ipos1, ipos2, icomp1, icomp2)``, where ``icomp1`` is the position
    of the component tensor with contravariant index, ``ipos1`` is the
    slot which the index occupies in that component tensor.

    Contracted indices are therefore nameless in the internal representation.
    """

    _op_priority = 12.0
    is_commutative = False

    def __neg__(self):
        return self*S.NegativeOne

    def __abs__(self):
        raise NotImplementedError

    def __add__(self, other):
        return TensAdd(self, other).doit()

    def __radd__(self, other):
        return TensAdd(other, self).doit()

    def __sub__(self, other):
        return TensAdd(self, -other).doit()

    def __rsub__(self, other):
        return TensAdd(other, -self).doit()

    def __mul__(self, other):
        """
        Multiply two tensors using Einstein summation convention.

        If the two tensors have an index in common, one contravariant
        and the other covariant, in their product the indices are summed

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> g = Lorentz.metric
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> t1 = p(m0)
        >>> t2 = q(-m0)
        >>> t1*t2
        p(L_0)*q(-L_0)
        """
        return TensMul(self, other).doit()

    def __rmul__(self, other):
        return TensMul(other, self).doit()

    def __div__(self, other):
        other = _sympify(other)
        if isinstance(other, TensExpr):
            raise ValueError('cannot divide by a tensor')
        return TensMul(self, S.One/other).doit()

    def __rdiv__(self, other):
        raise ValueError('cannot divide by a tensor')

    def __pow__(self, other):
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
            if self.data is None:
                raise ValueError("No power without ndarray data.")
        deprecate_data()
        from .array import tensorproduct, tensorcontraction
        free = self.free
        marray = self.data
        mdim = marray.rank()
        for metric in free:
            marray = tensorcontraction(
                tensorproduct(
                marray,
                metric[0].tensor_index_type.data,
                marray),
                (0, mdim), (mdim+1, mdim+2)
            )
        return marray ** (Rational(1, 2) * other)

    def __rpow__(self, other):
        raise NotImplementedError

    __truediv__ = __div__
    __rtruediv__ = __rdiv__

    def fun_eval(self, *index_tuples):
        """
        Return a tensor with free indices substituted according to ``index_tuples``

        ``index_types`` list of tuples ``(old_index, new_index)``

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
        >>> A, B = tensorhead('A,B', [Lorentz]*2, [[1]*2])
        >>> t = A(i, k)*B(-k, -j); t
        A(i, L_0)*B(-L_0, -j)
        >>> t.fun_eval((i, k),(-j, l))
        A(k, L_0)*B(-L_0, l)
        """
        expr = self.xreplace(dict(index_tuples))
        expr = expr.replace(lambda x: isinstance(x, Tensor), lambda x: x.args[0](*x.args[1]))
        # For some reason, `TensMul` gets replaced by `Mul`, correct it:
        expr = expr.replace(lambda x: isinstance(x, (Mul, TensMul)), lambda x: TensMul(*x.args).doit())
        return expr

    def get_matrix(self):
        """
        DEPRECATED: do not use.

        Returns ndarray components data as a matrix, if components data are
        available and ndarray dimension does not exceed 2.
        """
        from sympy import Matrix
        deprecate_data()
        if 0 < self.rank <= 2:
            rows = self.data.shape[0]
            columns = self.data.shape[1] if self.rank == 2 else 1
            if self.rank == 2:
                mat_list = [] * rows
                for i in range(rows):
                    mat_list.append([])
                    for j in range(columns):
                        mat_list[i].append(self[i, j])
            else:
                mat_list = [None] * rows
                for i in range(rows):
                    mat_list[i] = self[i]
            return Matrix(mat_list)
        else:
            raise NotImplementedError(
                "missing multidimensional reduction to matrix.")

    @staticmethod
    def _get_indices_permutation(indices1, indices2):
        return [indices1.index(i) for i in indices2]

    def expand(self, **hints):
        return _expand(self, **hints).doit()

    def _expand(self, **kwargs):
        return self

    def _get_free_indices_set(self):
        indset = set([])
        for arg in self.args:
            if isinstance(arg, TensExpr):
                indset.update(arg._get_free_indices_set())
        return indset

    def _get_dummy_indices_set(self):
        indset = set([])
        for arg in self.args:
            if isinstance(arg, TensExpr):
                indset.update(arg._get_dummy_indices_set())
        return indset

    def _get_indices_set(self):
        indset = set([])
        for arg in self.args:
            if isinstance(arg, TensExpr):
                indset.update(arg._get_indices_set())
        return indset

    @property
    def _iterate_dummy_indices(self):
        dummy_set = self._get_dummy_indices_set()

        def recursor(expr, pos):
            if isinstance(expr, TensorIndex):
                if expr in dummy_set:
                    yield (expr, pos)
            elif isinstance(expr, (Tuple, TensExpr)):
                for p, arg in enumerate(expr.args):
                    for i in recursor(arg, pos+(p,)):
                        yield i

        return recursor(self, ())

    @property
    def _iterate_free_indices(self):
        free_set = self._get_free_indices_set()

        def recursor(expr, pos):
            if isinstance(expr, TensorIndex):
                if expr in free_set:
                    yield (expr, pos)
            elif isinstance(expr, (Tuple, TensExpr)):
                for p, arg in enumerate(expr.args):
                    for i in recursor(arg, pos+(p,)):
                        yield i

        return recursor(self, ())

    @property
    def _iterate_indices(self):
        def recursor(expr, pos):
            if isinstance(expr, TensorIndex):
                yield (expr, pos)
            elif isinstance(expr, (Tuple, TensExpr)):
                for p, arg in enumerate(expr.args):
                    for i in recursor(arg, pos+(p,)):
                        yield i

        return recursor(self, ())

    @staticmethod
    def _match_indices_with_other_tensor(array, free_ind1, free_ind2, replacement_dict):
        from .array import tensorcontraction, tensorproduct, permutedims

        index_types1 = [i.tensor_index_type for i in free_ind1]

        # Check if variance of indices needs to be fixed:
        pos2up = []
        pos2down = []
        free2remaining = free_ind2[:]
        for pos1, index1 in enumerate(free_ind1):
            if index1 in free2remaining:
                pos2 = free2remaining.index(index1)
                free2remaining[pos2] = None
                continue
            if -index1 in free2remaining:
                pos2 = free2remaining.index(-index1)
                free2remaining[pos2] = None
                free_ind2[pos2] = index1
                if index1.is_up:
                    pos2up.append(pos2)
                else:
                    pos2down.append(pos2)
            else:
                index2 = free2remaining[pos1]
                if index2 is None:
                    raise ValueError("incompatible indices: %s and %s" % (free_ind1, free_ind2))
                free2remaining[pos1] = None
                free_ind2[pos1] = index1
                if index1.is_up ^ index2.is_up:
                    if index1.is_up:
                        pos2up.append(pos1)
                    else:
                        pos2down.append(pos1)

        if len(set(free_ind1) & set(free_ind2)) < len(free_ind1):
            raise ValueError("incompatible indices: %s and %s" % (free_ind1, free_ind2))

        # TODO: add possibility of metric after (spinors)
        def contract_and_permute(metric, array, pos):
            array = tensorcontraction(tensorproduct(metric, array), (1, 2+pos))
            permu = list(range(len(free_ind1)))
            permu[0], permu[pos] = permu[pos], permu[0]
            return permutedims(array, permu)

        # Raise indices:
        for pos in pos2up:
            metric = replacement_dict[index_types1[pos]]
            metric_inverse = _TensorDataLazyEvaluator.inverse_matrix(metric)
            array = contract_and_permute(metric_inverse, array, pos)
        # Lower indices:
        for pos in pos2down:
            metric = replacement_dict[index_types1[pos]]
            array = contract_and_permute(metric, array, pos)

        if free_ind1:
            permutation = TensExpr._get_indices_permutation(free_ind2, free_ind1)
            array = permutedims(array, permutation)

        if hasattr(array, "rank") and array.rank() == 0:
            array = array[()]

        return free_ind2, array

    def replace_with_arrays(self, replacement_dict, indices=None):
        """
        Replace the tensorial expressions with arrays. The final array will
        correspond to the N-dimensional array with indices arranged according
        to ``indices``.

        Parameters
        ==========

        replacement_dict
            dictionary containing the replacement rules for tensors.
        indices
            the index order with respect to which the array is read. The
            original index order will be used if no value is passed.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices
        >>> from sympy.tensor.tensor import tensorhead
        >>> from sympy import symbols, diag

        >>> L = TensorIndexType("L")
        >>> i, j = tensor_indices("i j", L)
        >>> A = tensorhead("A", [L], [[1]])
        >>> A(i).replace_with_arrays({A(i): [1, 2]}, [i])
        [1, 2]

        Since 'indices' is optional, we can also call replace_with_arrays by
        this way if no specific index order is needed:

        >>> A(i).replace_with_arrays({A(i): [1, 2]})
        [1, 2]

        >>> expr = A(i)*A(j)
        >>> expr.replace_with_arrays({A(i): [1, 2]})
        [[1, 2], [2, 4]]

        For contractions, specify the metric of the ``TensorIndexType``, which
        in this case is ``L``, in its covariant form:

        >>> expr = A(i)*A(-i)
        >>> expr.replace_with_arrays({A(i): [1, 2], L: diag(1, -1)})
        -3

        Symmetrization of an array:

        >>> H = tensorhead("H", [L, L], [[1], [1]])
        >>> a, b, c, d = symbols("a b c d")
        >>> expr = H(i, j)/2 + H(j, i)/2
        >>> expr.replace_with_arrays({H(i, j): [[a, b], [c, d]]})
        [[a, b/2 + c/2], [b/2 + c/2, d]]

        Anti-symmetrization of an array:

        >>> expr = H(i, j)/2 - H(j, i)/2
        >>> repl = {H(i, j): [[a, b], [c, d]]}
        >>> expr.replace_with_arrays(repl)
        [[0, b/2 - c/2], [-b/2 + c/2, 0]]

        The same expression can be read as the transpose by inverting ``i`` and
        ``j``:

        >>> expr.replace_with_arrays(repl, [j, i])
        [[0, -b/2 + c/2], [b/2 - c/2, 0]]
        """
        from .array import Array

        indices = indices or []
        replacement_dict = {tensor: Array(array) for tensor, array in replacement_dict.items()}

        # Check dimensions of replaced arrays:
        for tensor, array in replacement_dict.items():
            if isinstance(tensor, TensorIndexType):
                expected_shape = [tensor.dim for i in range(2)]
            else:
                expected_shape = [index_type.dim for index_type in tensor.index_types]
            if len(expected_shape) != array.rank() or (not all([dim1 == dim2 if
                dim1 is not None else True for dim1, dim2 in zip(expected_shape,
                array.shape)])):
                raise ValueError("shapes for tensor %s expected to be %s, "\
                    "replacement array shape is %s" % (tensor, expected_shape,
                    array.shape))

        ret_indices, array = self._extract_data(replacement_dict)

        last_indices, array = self._match_indices_with_other_tensor(array, indices, ret_indices, replacement_dict)
        #permutation = self._get_indices_permutation(indices, ret_indices)
        #if not hasattr(array, "rank"):
            #return array
        #if array.rank() == 0:
            #array = array[()]
            #return array
        #array = permutedims(array, permutation)
        return array

    def _check_add_Sum(self, expr, index_symbols):
        from sympy import Sum
        indices = self.get_indices()
        dum = self.dum
        sum_indices = [ (index_symbols[i], 0,
            indices[i].tensor_index_type.dim-1) for i, j in dum]
        if sum_indices:
            expr = Sum(expr, *sum_indices)
        return expr


class TensAdd(TensExpr, AssocOp):
    """
    Sum of tensors

    Parameters
    ==========

    free_args : list of the free indices

    Attributes
    ==========

    ``args`` : tuple of addends
    ``rank`` : rank of the tensor
    ``free_args`` : list of the free indices in sorted order

    Notes
    =====

    Sum of more than one tensor are put automatically in canonical form.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensorhead, tensor_indices
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b = tensor_indices('a,b', Lorentz)
    >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
    >>> t = p(a) + q(a); t
    p(a) + q(a)
    >>> t(b)
    p(b) + q(b)

    Examples with components data added to the tensor expression:

    >>> from sympy import symbols, diag
    >>> x, y, z, t = symbols("x y z t")
    >>> repl = {}
    >>> repl[Lorentz] = diag(1, -1, -1, -1)
    >>> repl[p(a)] = [1, 2, 3, 4]
    >>> repl[q(a)] = [x, y, z, t]

    The following are: 2**2 - 3**2 - 2**2 - 7**2 ==> -58

    >>> expr = p(a) + q(a)
    >>> expr.replace_with_arrays(repl, [a])
    [x + 1, y + 2, z + 3, t + 4]
    """

    def __new__(cls, *args, **kw_args):
        args = [_sympify(x) for x in args if x]

        args = TensAdd._tensAdd_flatten(args)

        obj = Basic.__new__(cls, *args, **kw_args)
        return obj

    def doit(self, **kwargs):
        deep = kwargs.get('deep', True)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args

        if not args:
            return S.Zero

        if len(args) == 1 and not isinstance(args[0], TensExpr):
            return args[0]

        # now check that all addends have the same indices:
        TensAdd._tensAdd_check(args)

        # if TensAdd has only 1 element in its `args`:
        if len(args) == 1:  # and isinstance(args[0], TensMul):
            return args[0]

        # Remove zeros:
        args = [x for x in args if x]

        # if there are no more args (i.e. have cancelled out),
        # just return zero:
        if not args:
            return S.Zero

        if len(args) == 1:
            return args[0]

        # Collect terms appearing more than once, differing by their coefficients:
        args = TensAdd._tensAdd_collect_terms(args)

        # collect canonicalized terms
        def sort_key(t):
            x = get_index_structure(t)
            if not isinstance(t, TensExpr):
                return ([], [], [])
            return (t.components, x.free, x.dum)
        args.sort(key=sort_key)

        if not args:
            return S.Zero
        # it there is only a component tensor return it
        if len(args) == 1:
            return args[0]

        obj = self.func(*args)
        return obj

    @staticmethod
    def _tensAdd_flatten(args):
        # flatten TensAdd, coerce terms which are not tensors to tensors
        a = []
        for x in args:
            if isinstance(x, (Add, TensAdd)):
                a.extend(list(x.args))
            else:
                a.append(x)
        args = [x for x in a if x.coeff]
        return args

    @staticmethod
    def _tensAdd_check(args):
        # check that all addends have the same free indices
        indices0 = set([x[0] for x in get_index_structure(args[0]).free])
        list_indices = [set([y[0] for y in get_index_structure(x).free]) for x in args[1:]]
        if not all(x == indices0 for x in list_indices):
            raise ValueError('all tensors must have the same indices')

    @staticmethod
    def _tensAdd_collect_terms(args):
        # collect TensMul terms differing at most by their coefficient
        terms_dict = defaultdict(list)
        scalars = S.Zero
        if isinstance(args[0], TensExpr):
            free_indices = set(args[0].get_free_indices())
        else:
            free_indices = set([])

        for arg in args:
            if not isinstance(arg, TensExpr):
                if free_indices != set([]):
                    raise ValueError("wrong valence")
                scalars += arg
                continue
            if free_indices != set(arg.get_free_indices()):
                raise ValueError("wrong valence")
            # TODO: what is the part which is not a coeff?
            # needs an implementation similar to .as_coeff_Mul()
            terms_dict[arg.nocoeff].append(arg.coeff)

        new_args = [TensMul(Add(*coeff), t).doit() for t, coeff in terms_dict.items() if Add(*coeff) != 0]
        if isinstance(scalars, Add):
            new_args = list(scalars.args) + new_args
        elif scalars != 0:
            new_args = [scalars] + new_args
        return new_args

    def get_indices(self):
        indices = []
        for arg in self.args:
            indices.extend([i for i in get_indices(arg) if i not in indices])
        return indices

    @property
    def rank(self):
        return self.args[0].rank

    @property
    def free_args(self):
        return self.args[0].free_args

    def _expand(self, **hints):
        return TensAdd(*[_expand(i, **hints) for i in self.args])

    def __call__(self, *indices):
        """Returns tensor with ordered free indices replaced by ``indices``

        Parameters
        ==========

        indices

        Examples
        ========

        >>> from sympy import Symbol
        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> D = Symbol('D')
        >>> Lorentz = TensorIndexType('Lorentz', dim=D, dummy_fmt='L')
        >>> i0,i1,i2,i3,i4 = tensor_indices('i0:5', Lorentz)
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> g = Lorentz.metric
        >>> t = p(i0)*p(i1) + g(i0,i1)*q(i2)*q(-i2)
        >>> t(i0,i2)
        metric(i0, i2)*q(L_0)*q(-L_0) + p(i0)*p(i2)
        >>> from sympy.tensor.tensor import canon_bp
        >>> canon_bp(t(i0,i1) - t(i1,i0))
        0
        """
        free_args = self.free_args
        indices = list(indices)
        if [x.tensor_index_type for x in indices] != [x.tensor_index_type for x in free_args]:
            raise ValueError('incompatible types')
        if indices == free_args:
            return self
        index_tuples = list(zip(free_args, indices))
        a = [x.func(*x.fun_eval(*index_tuples).args) for x in self.args]
        res = TensAdd(*a).doit()
        return res

    def canon_bp(self):
        """
        canonicalize using the Butler-Portugal algorithm for canonicalization
        under monoterm symmetries.
        """
        expr = self.expand()
        args = [canon_bp(x) for x in expr.args]
        res = TensAdd(*args).doit()
        return res

    def equals(self, other):
        other = _sympify(other)
        if isinstance(other, TensMul) and other._coeff == 0:
            return all(x._coeff == 0 for x in self.args)
        if isinstance(other, TensExpr):
            if self.rank != other.rank:
                return False
        if isinstance(other, TensAdd):
            if set(self.args) != set(other.args):
                return False
            else:
                return True
        t = self - other
        if not isinstance(t, TensExpr):
            return t == 0
        else:
            if isinstance(t, TensMul):
                return t._coeff == 0
            else:
                return all(x._coeff == 0 for x in t.args)

    def __getitem__(self, item):
        deprecate_data()
        return self.data[item]

    def contract_delta(self, delta):
        args = [x.contract_delta(delta) for x in self.args]
        t = TensAdd(*args).doit()
        return canon_bp(t)

    def contract_metric(self, g):
        """
        Raise or lower indices with the metric ``g``

        Parameters
        ==========

        g :  metric

        contract_all : if True, eliminate all ``g`` which are contracted

        Notes
        =====

        see the ``TensorIndexType`` docstring for the contraction conventions
        """

        args = [contract_metric(x, g) for x in self.args]
        t = TensAdd(*args).doit()
        return canon_bp(t)

    def fun_eval(self, *index_tuples):
        """
        Return a tensor with free indices substituted according to ``index_tuples``

        Parameters
        ==========

        index_types : list of tuples ``(old_index, new_index)``

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
        >>> A, B = tensorhead('A,B', [Lorentz]*2, [[1]*2])
        >>> t = A(i, k)*B(-k, -j) + A(i, -j)
        >>> t.fun_eval((i, k),(-j, l))
        A(k, L_0)*B(-L_0, l) + A(k, l)
        """
        args = self.args
        args1 = []
        for x in args:
            y = x.fun_eval(*index_tuples)
            args1.append(y)
        return TensAdd(*args1).doit()

    def substitute_indices(self, *index_tuples):
        """
        Return a tensor with free indices substituted according to ``index_tuples``

        Parameters
        ==========

        index_types : list of tuples ``(old_index, new_index)``

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
        >>> A, B = tensorhead('A,B', [Lorentz]*2, [[1]*2])
        >>> t = A(i, k)*B(-k, -j); t
        A(i, L_0)*B(-L_0, -j)
        >>> t.substitute_indices((i,j), (j, k))
        A(j, L_0)*B(-L_0, -k)
        """
        args = self.args
        args1 = []
        for x in args:
            y = x.substitute_indices(*index_tuples)
            args1.append(y)
        return TensAdd(*args1).doit()

    def _print(self):
        a = []
        args = self.args
        for x in args:
            a.append(str(x))
        a.sort()
        s = ' + '.join(a)
        s = s.replace('+ -', '- ')
        return s

    def _extract_data(self, replacement_dict):
        from sympy.tensor.array import Array, permutedims
        args_indices, arrays = zip(*[
            arg._extract_data(replacement_dict) if
            isinstance(arg, TensExpr) else ([], arg) for arg in self.args
        ])
        arrays = [Array(i) for i in arrays]
        ref_indices = args_indices[0]
        for i in range(1, len(args_indices)):
            indices = args_indices[i]
            array = arrays[i]
            permutation = TensMul._get_indices_permutation(indices, ref_indices)
            arrays[i] = permutedims(array, permutation)
        return ref_indices, sum(arrays, Array.zeros(*array.shape))

    @property
    def data(self):
        deprecate_data()
        return _tensor_data_substitution_dict[self.expand()]

    @data.setter
    def data(self, data):
        deprecate_data()
        _tensor_data_substitution_dict[self] = data

    @data.deleter
    def data(self):
        deprecate_data()
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]

    def __iter__(self):
        deprecate_data()
        if not self.data:
            raise ValueError("No iteration on abstract tensors")
        return self.data.flatten().__iter__()

    def _eval_rewrite_as_Indexed(self, *args):
        return Add.fromiter(args)


class Tensor(TensExpr):
    """
    Base tensor class, i.e. this represents a tensor, the single unit to be
    put into an expression.

    This object is usually created from a ``TensorHead``, by attaching indices
    to it. Indices preceded by a minus sign are considered contravariant,
    otherwise covariant.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
    >>> Lorentz = TensorIndexType("Lorentz", dummy_fmt="L")
    >>> mu, nu = tensor_indices('mu nu', Lorentz)
    >>> A = tensorhead("A", [Lorentz, Lorentz], [[1], [1]])
    >>> A(mu, -nu)
    A(mu, -nu)
    >>> A(mu, -mu)
    A(L_0, -L_0)

    """

    is_commutative = False

    def __new__(cls, tensor_head, indices, **kw_args):
        is_canon_bp = kw_args.pop('is_canon_bp', False)
        indices = cls._parse_indices(tensor_head, indices)
        obj = Basic.__new__(cls, tensor_head, Tuple(*indices), **kw_args)
        obj._index_structure = _IndexStructure.from_indices(*indices)
        obj._free_indices_set = set(obj._index_structure.get_free_indices())
        if tensor_head.rank != len(indices):
            raise ValueError("wrong number of indices")
        obj._indices = indices
        obj._is_canon_bp = is_canon_bp
        obj._index_map = Tensor._build_index_map(indices, obj._index_structure)
        return obj

    @staticmethod
    def _build_index_map(indices, index_structure):
        index_map = {}
        for idx in indices:
            index_map[idx] = (indices.index(idx),)
        return index_map

    def doit(self, **kwargs):
        args, indices, free, dum = TensMul._tensMul_contract_indices([self])
        return args[0]

    @staticmethod
    def _parse_indices(tensor_head, indices):
        if not isinstance(indices, (tuple, list, Tuple)):
            raise TypeError("indices should be an array, got %s" % type(indices))
        indices = list(indices)
        for i, index in enumerate(indices):
            if isinstance(index, Symbol):
                indices[i] = TensorIndex(index, tensor_head.index_types[i], True)
            elif isinstance(index, Mul):
                c, e = index.as_coeff_Mul()
                if c == -1 and isinstance(e, Symbol):
                    indices[i] = TensorIndex(e, tensor_head.index_types[i], False)
                else:
                    raise ValueError("index not understood: %s" % index)
            elif not isinstance(index, TensorIndex):
                raise TypeError("wrong type for index: %s is %s" % (index, type(index)))
        return indices

    def _set_new_index_structure(self, im, is_canon_bp=False):
        indices = im.get_indices()
        return self._set_indices(*indices, is_canon_bp=is_canon_bp)

    def _set_indices(self, *indices, **kw_args):
        if len(indices) != self.ext_rank:
            raise ValueError("indices length mismatch")
        return self.func(self.args[0], indices, is_canon_bp=kw_args.pop('is_canon_bp', False)).doit()

    def _get_free_indices_set(self):
        return set([i[0] for i in self._index_structure.free])

    def _get_dummy_indices_set(self):
        dummy_pos = set(itertools.chain(*self._index_structure.dum))
        return set(idx for i, idx in enumerate(self.args[1]) if i in dummy_pos)

    def _get_indices_set(self):
        return set(self.args[1].args)

    @property
    def is_canon_bp(self):
        return self._is_canon_bp

    @property
    def indices(self):
        return self._indices

    @property
    def free(self):
        return self._index_structure.free[:]

    @property
    def free_in_args(self):
        return [(ind, pos, 0) for ind, pos in self.free]

    @property
    def dum(self):
        return self._index_structure.dum[:]

    @property
    def dum_in_args(self):
        return [(p1, p2, 0, 0) for p1, p2 in self.dum]

    @property
    def rank(self):
        return len(self.free)

    @property
    def ext_rank(self):
        return self._index_structure._ext_rank

    @property
    def free_args(self):
        return sorted([x[0] for x in self.free])

    def commutes_with(self, other):
        """
        :param other:
        :return:
            0  commute
            1  anticommute
            None  neither commute nor anticommute
        """
        if not isinstance(other, TensExpr):
            return 0
        elif isinstance(other, Tensor):
            return self.component.commutes_with(other.component)
        return NotImplementedError

    def perm2tensor(self, g, is_canon_bp=False):
        """
        Returns the tensor corresponding to the permutation ``g``

        For further details, see the method in ``TIDS`` with the same name.
        """
        return perm2tensor(self, g, is_canon_bp)

    def canon_bp(self):
        if self._is_canon_bp:
            return self
        expr = self.expand()
        g, dummies, msym = expr._index_structure.indices_canon_args()
        v = components_canon_args([expr.component])
        can = canonicalize(g, dummies, msym, *v)
        if can == 0:
            return S.Zero
        tensor = self.perm2tensor(can, True)
        return tensor

    @property
    def index_types(self):
        return list(self.component.index_types)

    @property
    def coeff(self):
        return S.One

    @property
    def nocoeff(self):
        return self

    @property
    def component(self):
        return self.args[0]

    @property
    def components(self):
        return [self.args[0]]

    def split(self):
        return [self]

    def _expand(self, **kwargs):
        return self

    def sorted_components(self):
        return self

    def get_indices(self):
        """
        Get a list of indices, corresponding to those of the tensor.
        """
        return list(self.args[1])

    def get_free_indices(self):
        """
        Get a list of free indices, corresponding to those of the tensor.
        """
        return self._index_structure.get_free_indices()

    def as_base_exp(self):
        return self, S.One

    def substitute_indices(self, *index_tuples):
        return substitute_indices(self, *index_tuples)

    def __call__(self, *indices):
        """Returns tensor with ordered free indices replaced by ``indices``

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> i0,i1,i2,i3,i4 = tensor_indices('i0:5', Lorentz)
        >>> A = tensorhead('A', [Lorentz]*5, [[1]*5])
        >>> t = A(i2, i1, -i2, -i3, i4)
        >>> t
        A(L_0, i1, -L_0, -i3, i4)
        >>> t(i1, i2, i3)
        A(L_0, i1, -L_0, i2, i3)
        """

        free_args = self.free_args
        indices = list(indices)
        if [x.tensor_index_type for x in indices] != [x.tensor_index_type for x in free_args]:
            raise ValueError('incompatible types')
        if indices == free_args:
            return self
        t = self.fun_eval(*list(zip(free_args, indices)))

        # object is rebuilt in order to make sure that all contracted indices
        # get recognized as dummies, but only if there are contracted indices.
        if len(set(i if i.is_up else -i for i in indices)) != len(indices):
            return t.func(*t.args)
        return t

    # TODO: put this into TensExpr?
    def __iter__(self):
        deprecate_data()
        return self.data.__iter__()

    # TODO: put this into TensExpr?
    def __getitem__(self, item):
        deprecate_data()
        return self.data[item]

    def _extract_data(self, replacement_dict):
        from .array import Array
        for k, v in replacement_dict.items():
            if isinstance(k, Tensor) and k.args[0] == self.args[0]:
                other = k
                array = v
                break
        else:
            raise ValueError("%s not found in %s" % (self, replacement_dict))

        # TODO: inefficient, this should be done at root level only:
        replacement_dict = {k: Array(v) for k, v in replacement_dict.items()}
        array = Array(array)

        dum1 = self.dum
        dum2 = other.dum

        if len(dum2) > 0:
            for pair in dum2:
                # allow `dum2` if the contained values are also in `dum1`.
                if pair not in dum1:
                    raise NotImplementedError("%s with contractions is not implemented" % other)
            # Remove elements in `dum2` from `dum1`:
            dum1 = [pair for pair in dum1 if pair not in dum2]
        if len(dum1) > 0:
            indices2 = other.get_indices()
            repl = {}
            for p1, p2 in dum1:
                repl[indices2[p2]] = -indices2[p1]
            other = other.xreplace(repl).doit()
            array = _TensorDataLazyEvaluator.data_contract_dum([array], dum1, len(indices2))

        free_ind1 = self.get_free_indices()
        free_ind2 = other.get_free_indices()

        return self._match_indices_with_other_tensor(array, free_ind1, free_ind2, replacement_dict)

    @property
    def data(self):
        deprecate_data()
        return _tensor_data_substitution_dict[self]

    @data.setter
    def data(self, data):
        deprecate_data()
        # TODO: check data compatibility with properties of tensor.
        _tensor_data_substitution_dict[self] = data

    @data.deleter
    def data(self):
        deprecate_data()
        if self in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self]
        if self.metric in _tensor_data_substitution_dict:
            del _tensor_data_substitution_dict[self.metric]

    def _print(self):
        indices = [str(ind) for ind in self.indices]
        component = self.component
        if component.rank > 0:
            return ('%s(%s)' % (component.name, ', '.join(indices)))
        else:
            return ('%s' % component.name)

    def equals(self, other):
        if other == 0:
            return self.coeff == 0
        other = _sympify(other)
        if not isinstance(other, TensExpr):
            assert not self.components
            return S.One == other

        def _get_compar_comp(self):
            t = self.canon_bp()
            r = (t.coeff, tuple(t.components), \
                    tuple(sorted(t.free)), tuple(sorted(t.dum)))
            return r

        return _get_compar_comp(self) == _get_compar_comp(other)

    def contract_metric(self, g):
        # if metric is not the same, ignore this step:
        if self.component != g:
            return self
        # in case there are free components, do not perform anything:
        if len(self.free) != 0:
            return self

        antisym = g.index_types[0].metric_antisym
        sign = S.One
        typ = g.index_types[0]

        if not antisym:
            # g(i, -i)
            if typ._dim is None:
                raise ValueError('dimension not assigned')
            sign = sign*typ._dim
        else:
            # g(i, -i)
            if typ._dim is None:
                raise ValueError('dimension not assigned')
            sign = sign*typ._dim

            dp0, dp1 = self.dum[0]
            if dp0 < dp1:
                # g(i, -i) = -D with antisymmetric metric
                sign = -sign

        return sign

    def contract_delta(self, metric):
        return self.contract_metric(metric)

    def _eval_rewrite_as_Indexed(self, tens, indices):
        from sympy import Indexed
        # TODO: replace .args[0] with .name:
        index_symbols = [i.args[0] for i in self.get_indices()]
        expr = Indexed(tens.args[0], *index_symbols)
        return self._check_add_Sum(expr, index_symbols)


class TensMul(TensExpr, AssocOp):
    """
    Product of tensors

    Parameters
    ==========

    coeff : SymPy coefficient of the tensor
    args

    Attributes
    ==========

    ``components`` : list of ``TensorHead`` of the component tensors
    ``types`` : list of nonrepeated ``TensorIndexType``
    ``free`` : list of ``(ind, ipos, icomp)``, see Notes
    ``dum`` : list of ``(ipos1, ipos2, icomp1, icomp2)``, see Notes
    ``ext_rank`` : rank of the tensor counting the dummy indices
    ``rank`` : rank of the tensor
    ``coeff`` : SymPy coefficient of the tensor
    ``free_args`` : list of the free indices in sorted order
    ``is_canon_bp`` : ``True`` if the tensor in in canonical form

    Notes
    =====

    ``args[0]``   list of ``TensorHead`` of the component tensors.

    ``args[1]``   list of ``(ind, ipos, icomp)``
    where ``ind`` is a free index, ``ipos`` is the slot position
    of ``ind`` in the ``icomp``-th component tensor.

    ``args[2]`` list of tuples representing dummy indices.
    ``(ipos1, ipos2, icomp1, icomp2)`` indicates that the contravariant
    dummy index is the ``ipos1``-th slot position in the ``icomp1``-th
    component tensor; the corresponding covariant index is
    in the ``ipos2`` slot position in the ``icomp2``-th component tensor.

    """
    identity = S.One

    def __new__(cls, *args, **kw_args):
        is_canon_bp = kw_args.get('is_canon_bp', False)
        args = list(map(_sympify, args))

        # Flatten:
        args = [i for arg in args for i in (arg.args if isinstance(arg, (TensMul, Mul)) else [arg])]

        args, indices, free, dum = TensMul._tensMul_contract_indices(args, replace_indices=False)

        # Data for indices:
        index_types = [i.tensor_index_type for i in indices]
        index_structure = _IndexStructure(free, dum, index_types, indices, canon_bp=is_canon_bp)

        obj = TensExpr.__new__(cls, *args)
        obj._indices = indices
        obj._index_types = index_types
        obj._index_structure = index_structure
        obj._ext_rank = len(obj._index_structure.free) + 2*len(obj._index_structure.dum)
        obj._coeff = S.One
        obj._is_canon_bp = is_canon_bp
        return obj

    @staticmethod
    def _indices_to_free_dum(args_indices):
        free2pos1 = {}
        free2pos2 = {}
        dummy_data = []
        indices = []

        # Notation for positions (to better understand the code):
        # `pos1`: position in the `args`.
        # `pos2`: position in the indices.

        # Example:
        # A(i, j)*B(k, m, n)*C(p)
        # `pos1` of `n` is 1 because it's in `B` (second `args` of TensMul).
        # `pos2` of `n` is 4 because it's the fifth overall index.

        # Counter for the index position wrt the whole expression:
        pos2 = 0

        for pos1, arg_indices in enumerate(args_indices):

            for index_pos, index in enumerate(arg_indices):
                if not isinstance(index, TensorIndex):
                    raise TypeError("expected TensorIndex")
                if -index in free2pos1:
                    # Dummy index detected:
                    other_pos1 = free2pos1.pop(-index)
                    other_pos2 = free2pos2.pop(-index)
                    if index.is_up:
                        dummy_data.append((index, pos1, other_pos1, pos2, other_pos2))
                    else:
                        dummy_data.append((-index, other_pos1, pos1, other_pos2, pos2))
                    indices.append(index)
                elif index in free2pos1:
                    raise ValueError("Repeated index: %s" % index)
                else:
                    free2pos1[index] = pos1
                    free2pos2[index] = pos2
                    indices.append(index)
                pos2 += 1

        free = [(i, p) for (i, p) in free2pos2.items()]
        free_names = [i.name for i in free2pos2.keys()]

        dummy_data.sort(key=lambda x: x[3])
        return indices, free, free_names, dummy_data

    @staticmethod
    def _dummy_data_to_dum(dummy_data):
        return [(p2a, p2b) for (i, p1a, p1b, p2a, p2b) in dummy_data]

    @staticmethod
    def _tensMul_contract_indices(args, replace_indices=True):
        replacements = [{} for _ in args]

        #_index_order = all([_has_index_order(arg) for arg in args])

        args_indices = [get_indices(arg) for arg in args]
        indices, free, free_names, dummy_data = TensMul._indices_to_free_dum(args_indices)

        cdt = defaultdict(int)

        def dummy_fmt_gen(tensor_index_type):
            fmt = tensor_index_type.dummy_fmt
            nd = cdt[tensor_index_type]
            cdt[tensor_index_type] += 1
            return fmt % nd

        if replace_indices:
            for old_index, pos1cov, pos1contra, pos2cov, pos2contra in dummy_data:
                index_type = old_index.tensor_index_type
                while True:
                    dummy_name = dummy_fmt_gen(index_type)
                    if dummy_name not in free_names:
                        break
                dummy = TensorIndex(dummy_name, index_type, True)
                replacements[pos1cov][old_index] = dummy
                replacements[pos1contra][-old_index] = -dummy
                indices[pos2cov] = dummy
                indices[pos2contra] = -dummy
            args = [arg.xreplace(repl) for arg, repl in zip(args, replacements)]

        dum = TensMul._dummy_data_to_dum(dummy_data)
        return args, indices, free, dum

    @staticmethod
    def _get_components_from_args(args):
        """
        Get a list of ``Tensor`` objects having the same ``TIDS`` if multiplied
        by one another.
        """
        components = []
        for arg in args:
            if not isinstance(arg, TensExpr):
                continue
            if isinstance(arg, TensAdd):
                continue
            components.extend(arg.components)
        return components

    @staticmethod
    def _rebuild_tensors_list(args, index_structure):
        indices = index_structure.get_indices()
        #tensors = [None for i in components]  # pre-allocate list
        ind_pos = 0
        for i, arg in enumerate(args):
            if not isinstance(arg, TensExpr):
                continue
            prev_pos = ind_pos
            ind_pos += arg.ext_rank
            args[i] = Tensor(arg.component, indices[prev_pos:ind_pos])

    def doit(self, **kwargs):
        is_canon_bp = self._is_canon_bp
        deep = kwargs.get('deep', True)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args

        args = [arg for arg in args if arg != self.identity]

        # Extract non-tensor coefficients:
        coeff = reduce(lambda a, b: a*b, [arg for arg in args if not isinstance(arg, TensExpr)], S.One)
        args = [arg for arg in args if isinstance(arg, TensExpr)]

        if len(args) == 0:
            return coeff

        if coeff != self.identity:
            args = [coeff] + args
        if coeff == 0:
            return S.Zero

        if len(args) == 1:
            return args[0]

        args, indices, free, dum = TensMul._tensMul_contract_indices(args)

        # Data for indices:
        index_types = [i.tensor_index_type for i in indices]
        index_structure = _IndexStructure(free, dum, index_types, indices, canon_bp=is_canon_bp)

        obj = self.func(*args)
        obj._index_types = index_types
        obj._index_structure = index_structure
        obj._ext_rank = len(obj._index_structure.free) + 2*len(obj._index_structure.dum)
        obj._coeff = coeff
        obj._is_canon_bp = is_canon_bp
        return obj

    # TODO: this method should be private
    # TODO: should this method be renamed _from_components_free_dum ?
    @staticmethod
    def from_data(coeff, components, free, dum, **kw_args):
        return TensMul(coeff, *TensMul._get_tensors_from_components_free_dum(components, free, dum), **kw_args).doit()

    @staticmethod
    def _get_tensors_from_components_free_dum(components, free, dum):
        """
        Get a list of ``Tensor`` objects by distributing ``free`` and ``dum`` indices on the ``components``.
        """
        index_structure = _IndexStructure.from_components_free_dum(components, free, dum)
        indices = index_structure.get_indices()
        tensors = [None for i in components]  # pre-allocate list

        # distribute indices on components to build a list of tensors:
        ind_pos = 0
        for i, component in enumerate(components):
            prev_pos = ind_pos
            ind_pos += component.rank
            tensors[i] = Tensor(component, indices[prev_pos:ind_pos])
        return tensors

    def _get_free_indices_set(self):
        return set([i[0] for i in self.free])

    def _get_dummy_indices_set(self):
        dummy_pos = set(itertools.chain(*self.dum))
        return set(idx for i, idx in enumerate(self._index_structure.get_indices()) if i in dummy_pos)

    def _get_position_offset_for_indices(self):
        arg_offset = [None for i in range(self.ext_rank)]
        counter = 0
        for i, arg in enumerate(self.args):
            if not isinstance(arg, TensExpr):
                continue
            for j in range(arg.ext_rank):
                arg_offset[j + counter] = counter
            counter += arg.ext_rank
        return arg_offset

    @property
    def free_args(self):
        return sorted([x[0] for x in self.free])

    @property
    def components(self):
        return self._get_components_from_args(self.args)

    @property
    def free(self):
        return self._index_structure.free[:]

    @property
    def free_in_args(self):
        arg_offset = self._get_position_offset_for_indices()
        argpos = self._get_indices_to_args_pos()
        return [(ind, pos-arg_offset[pos], argpos[pos]) for (ind, pos) in self.free]

    @property
    def coeff(self):
        return self._coeff

    @property
    def nocoeff(self):
        return self.func(*[t for t in self.args if isinstance(t, TensExpr)]).doit()

    @property
    def dum(self):
        return self._index_structure.dum[:]

    @property
    def dum_in_args(self):
        arg_offset = self._get_position_offset_for_indices()
        argpos = self._get_indices_to_args_pos()
        return [(p1-arg_offset[p1], p2-arg_offset[p2], argpos[p1], argpos[p2]) for p1, p2 in self.dum]

    @property
    def rank(self):
        return len(self.free)

    @property
    def ext_rank(self):
        return self._ext_rank

    @property
    def index_types(self):
        return self._index_types[:]

    def equals(self, other):
        if other == 0:
            return self.coeff == 0
        other = _sympify(other)
        if not isinstance(other, TensExpr):
            assert not self.components
            return self._coeff == other

        return self.canon_bp() == other.canon_bp()

    def get_indices(self):
        """
        Returns the list of indices of the tensor

        The indices are listed in the order in which they appear in the
        component tensors.
        The dummy indices are given a name which does not collide with
        the names of the free indices.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> g = Lorentz.metric
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> t = p(m1)*g(m0,m2)
        >>> t.get_indices()
        [m1, m0, m2]
        >>> t2 = p(m1)*g(-m1, m2)
        >>> t2.get_indices()
        [L_0, -L_0, m2]
        """
        return self._indices

    def get_free_indices(self):
        """
        Returns the list of free indices of the tensor

        The indices are listed in the order in which they appear in the
        component tensors.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> g = Lorentz.metric
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> t = p(m1)*g(m0,m2)
        >>> t.get_free_indices()
        [m1, m0, m2]
        >>> t2 = p(m1)*g(-m1, m2)
        >>> t2.get_free_indices()
        [m2]
        """
        return self._index_structure.get_free_indices()

    def split(self):
        """
        Returns a list of tensors, whose product is ``self``

        Dummy indices contracted among different tensor components
        become free indices with the same name as the one used to
        represent the dummy indices.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
        >>> A, B = tensorhead('A,B', [Lorentz]*2, [[1]*2])
        >>> t = A(a,b)*B(-b,c)
        >>> t
        A(a, L_0)*B(-L_0, c)
        >>> t.split()
        [A(a, L_0), B(-L_0, c)]
        """
        if self.args == ():
            return [self]
        splitp = []
        res = 1
        for arg in self.args:
            if isinstance(arg, Tensor):
                splitp.append(res*arg)
                res = 1
            else:
                res *= arg
        return splitp

    def _expand(self, **hints):
        # TODO: temporary solution, in the future this should be linked to
        # `Expr.expand`.
        args = [_expand(arg, **hints) for arg in self.args]
        args1 = [arg.args if isinstance(arg, (Add, TensAdd)) else (arg,) for arg in args]
        return TensAdd(*[
            TensMul(*i) for i in itertools.product(*args1)]
        )

    def __neg__(self):
        return TensMul(S.NegativeOne, self, is_canon_bp=self._is_canon_bp).doit()

    def __getitem__(self, item):
        deprecate_data()
        return self.data[item]

    def _get_args_for_traditional_printer(self):
        args = list(self.args)
        if (self.coeff < 0) == True:
            # expressions like "-A(a)"
            sign = "-"
            if self.coeff == S.NegativeOne:
                args = args[1:]
            else:
                args[0] = -args[0]
        else:
            sign = ""
        return sign, args

    def _sort_args_for_sorted_components(self):
        """
        Returns the ``args`` sorted according to the components commutation
        properties.

        The sorting is done taking into account the commutation group
        of the component tensors.
        """
        cv = [arg for arg in self.args if isinstance(arg, TensExpr)]
        sign = 1
        n = len(cv) - 1
        for i in range(n):
            for j in range(n, i, -1):
                c = cv[j-1].commutes_with(cv[j])
                # if `c` is `None`, it does neither commute nor anticommute, skip:
                if c not in [0, 1]:
                    continue
                if (cv[j-1].component.types, cv[j-1].component.name) > \
                        (cv[j].component.types, cv[j].component.name):
                    cv[j-1], cv[j] = cv[j], cv[j-1]
                    # if `c` is 1, the anticommute, so change sign:
                    if c:
                        sign = -sign

        coeff = sign * self.coeff
        if coeff != 1:
            return [coeff] + cv
        return cv

    def sorted_components(self):
        """
        Returns a tensor product with sorted components.
        """
        return TensMul(*self._sort_args_for_sorted_components()).doit()

    def perm2tensor(self, g, is_canon_bp=False):
        """
        Returns the tensor corresponding to the permutation ``g``

        For further details, see the method in ``TIDS`` with the same name.
        """
        return perm2tensor(self, g, is_canon_bp=is_canon_bp)

    def canon_bp(self):
        """
        Canonicalize using the Butler-Portugal algorithm for canonicalization
        under monoterm symmetries.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> A = tensorhead('A', [Lorentz]*2, [[2]])
        >>> t = A(m0,-m1)*A(m1,-m0)
        >>> t.canon_bp()
        -A(L_0, L_1)*A(-L_0, -L_1)
        >>> t = A(m0,-m1)*A(m1,-m2)*A(m2,-m0)
        >>> t.canon_bp()
        0
        """
        if self._is_canon_bp:
            return self
        expr = self.expand()
        if isinstance(expr, TensAdd):
            return expr.canon_bp()
        if not expr.components:
            return expr
        t = expr.sorted_components()
        g, dummies, msym = t._index_structure.indices_canon_args()
        v = components_canon_args(t.components)
        can = canonicalize(g, dummies, msym, *v)
        if can == 0:
            return S.Zero
        tmul = t.perm2tensor(can, True)
        return tmul

    def contract_delta(self, delta):
        t = self.contract_metric(delta)
        return t

    def _get_indices_to_args_pos(self):
        """
        Get a dict mapping the index position to TensMul's argument number.
        """
        pos_map = dict()
        pos_counter = 0
        for arg_i, arg in enumerate(self.args):
            if not isinstance(arg, TensExpr):
                continue
            assert isinstance(arg, Tensor)
            for i in range(arg.ext_rank):
                pos_map[pos_counter] = arg_i
                pos_counter += 1
        return pos_map

    def contract_metric(self, g):
        """
        Raise or lower indices with the metric ``g``

        Parameters
        ==========

        g : metric

        Notes
        =====

        see the ``TensorIndexType`` docstring for the contraction conventions

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> g = Lorentz.metric
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> t = p(m0)*q(m1)*g(-m0, -m1)
        >>> t.canon_bp()
        metric(L_0, L_1)*p(-L_0)*q(-L_1)
        >>> t.contract_metric(g).canon_bp()
        p(L_0)*q(-L_0)
        """
        expr = self.expand()
        if self != expr:
            expr = expr.canon_bp()
            return expr.contract_metric(g)
        pos_map = self._get_indices_to_args_pos()
        args = list(self.args)

        antisym = g.index_types[0].metric_antisym

        # list of positions of the metric ``g`` inside ``args``
        gpos = [i for i, x in enumerate(self.args) if isinstance(x, Tensor) and x.component == g]
        if not gpos:
            return self

        # Sign is either 1 or -1, to correct the sign after metric contraction
        # (for spinor indices).
        sign = 1
        dum = self.dum[:]
        free = self.free[:]
        elim = set()
        for gposx in gpos:
            if gposx in elim:
                continue
            free1 = [x for x in free if pos_map[x[1]] == gposx]
            dum1 = [x for x in dum if pos_map[x[0]] == gposx or pos_map[x[1]] == gposx]
            if not dum1:
                continue
            elim.add(gposx)
            # subs with the multiplication neutral element, that is, remove it:
            args[gposx] = 1
            if len(dum1) == 2:
                if not antisym:
                    dum10, dum11 = dum1
                    if pos_map[dum10[1]] == gposx:
                        # the index with pos p0 contravariant
                        p0 = dum10[0]
                    else:
                        # the index with pos p0 is covariant
                        p0 = dum10[1]
                    if pos_map[dum11[1]] == gposx:
                        # the index with pos p1 is contravariant
                        p1 = dum11[0]
                    else:
                        # the index with pos p1 is covariant
                        p1 = dum11[1]

                    dum.append((p0, p1))
                else:
                    dum10, dum11 = dum1
                    # change the sign to bring the indices of the metric to contravariant
                    # form; change the sign if dum10 has the metric index in position 0
                    if pos_map[dum10[1]] == gposx:
                        # the index with pos p0 is contravariant
                        p0 = dum10[0]
                        if dum10[1] == 1:
                            sign = -sign
                    else:
                        # the index with pos p0 is covariant
                        p0 = dum10[1]
                        if dum10[0] == 0:
                            sign = -sign
                    if pos_map[dum11[1]] == gposx:
                        # the index with pos p1 is contravariant
                        p1 = dum11[0]
                        sign = -sign
                    else:
                        # the index with pos p1 is covariant
                        p1 = dum11[1]

                    dum.append((p0, p1))

            elif len(dum1) == 1:
                if not antisym:
                    dp0, dp1 = dum1[0]
                    if pos_map[dp0] == pos_map[dp1]:
                        # g(i, -i)
                        typ = g.index_types[0]
                        if typ._dim is None:
                            raise ValueError('dimension not assigned')
                        sign = sign*typ._dim

                    else:
                        # g(i0, i1)*p(-i1)
                        if pos_map[dp0] == gposx:
                            p1 = dp1
                        else:
                            p1 = dp0

                        ind, p = free1[0]
                        free.append((ind, p1))
                else:
                    dp0, dp1 = dum1[0]
                    if pos_map[dp0] == pos_map[dp1]:
                        # g(i, -i)
                        typ = g.index_types[0]
                        if typ._dim is None:
                            raise ValueError('dimension not assigned')
                        sign = sign*typ._dim

                        if dp0 < dp1:
                            # g(i, -i) = -D with antisymmetric metric
                            sign = -sign
                    else:
                        # g(i0, i1)*p(-i1)
                        if pos_map[dp0] == gposx:
                            p1 = dp1
                            if dp0 == 0:
                                sign = -sign
                        else:
                            p1 = dp0
                        ind, p = free1[0]
                        free.append((ind, p1))
            dum = [x for x in dum if x not in dum1]
            free = [x for x in free if x not in free1]

        # shift positions:
        shift = 0
        shifts = [0]*len(args)
        for i in range(len(args)):
            if i in elim:
                shift += 2
                continue
            shifts[i] = shift
        free = [(ind, p - shifts[pos_map[p]]) for (ind, p) in free if pos_map[p] not in elim]
        dum = [(p0 - shifts[pos_map[p0]], p1 - shifts[pos_map[p1]]) for i, (p0, p1) in enumerate(dum) if pos_map[p0] not in elim and pos_map[p1] not in elim]

        res = sign*TensMul(*args).doit()
        if not isinstance(res, TensExpr):
            return res
        im = _IndexStructure.from_components_free_dum(res.components, free, dum)
        return res._set_new_index_structure(im)

    def _set_new_index_structure(self, im, is_canon_bp=False):
        indices = im.get_indices()
        return self._set_indices(*indices, is_canon_bp=is_canon_bp)

    def _set_indices(self, *indices, **kw_args):
        if len(indices) != self.ext_rank:
            raise ValueError("indices length mismatch")
        args = list(self.args)[:]
        pos = 0
        is_canon_bp = kw_args.pop('is_canon_bp', False)
        for i, arg in enumerate(args):
            if not isinstance(arg, TensExpr):
                continue
            assert isinstance(arg, Tensor)
            ext_rank = arg.ext_rank
            args[i] = arg._set_indices(*indices[pos:pos+ext_rank])
            pos += ext_rank
        return TensMul(*args, is_canon_bp=is_canon_bp).doit()

    @staticmethod
    def _index_replacement_for_contract_metric(args, free, dum):
        for arg in args:
            if not isinstance(arg, TensExpr):
                continue
            assert isinstance(arg, Tensor)

    def substitute_indices(self, *index_tuples):
        return substitute_indices(self, *index_tuples)

    def __call__(self, *indices):
        """Returns tensor product with ordered free indices replaced by ``indices``

        Examples
        ========

        >>> from sympy import Symbol
        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
        >>> D = Symbol('D')
        >>> Lorentz = TensorIndexType('Lorentz', dim=D, dummy_fmt='L')
        >>> i0,i1,i2,i3,i4 = tensor_indices('i0:5', Lorentz)
        >>> g = Lorentz.metric
        >>> p, q = tensorhead('p,q', [Lorentz], [[1]])
        >>> t = p(i0)*q(i1)*q(-i1)
        >>> t(i1)
        p(i1)*q(L_0)*q(-L_0)
        """
        free_args = self.free_args
        indices = list(indices)
        if [x.tensor_index_type for x in indices] != [x.tensor_index_type for x in free_args]:
            raise ValueError('incompatible types')
        if indices == free_args:
            return self
        t = self.fun_eval(*list(zip(free_args, indices)))

        # object is rebuilt in order to make sure that all contracted indices
        # get recognized as dummies, but only if there are contracted indices.
        if len(set(i if i.is_up else -i for i in indices)) != len(indices):
            return t.func(*t.args)
        return t

    def _extract_data(self, replacement_dict):
        args_indices, arrays = zip(*[arg._extract_data(replacement_dict) for arg in self.args if isinstance(arg, TensExpr)])
        coeff = reduce(operator.mul, [a for a in self.args if not isinstance(a, TensExpr)], S.One)
        indices, free, free_names, dummy_data = TensMul._indices_to_free_dum(args_indices)
        dum = TensMul._dummy_data_to_dum(dummy_data)
        ext_rank = self.ext_rank
        free.sort(key=lambda x: x[1])
        free_indices = [i[0] for i in free]
        return free_indices, coeff*_TensorDataLazyEvaluator.data_contract_dum(arrays, dum, ext_rank)

    @property
    def data(self):
        deprecate_data()
        dat = _tensor_data_substitution_dict[self.expand()]
        return dat

    @data.setter
    def data(self, data):
        deprecate_data()
        raise ValueError("Not possible to set component data to a tensor expression")

    @data.deleter
    def data(self):
        deprecate_data()
        raise ValueError("Not possible to delete component data to a tensor expression")

    def __iter__(self):
        deprecate_data()
        if self.data is None:
            raise ValueError("No iteration on abstract tensors")
        return self.data.__iter__()

    def _eval_rewrite_as_Indexed(self, *args):
        from sympy import Sum
        index_symbols = [i.args[0] for i in self.get_indices()]
        args = [arg.args[0] if isinstance(arg, Sum) else arg for arg in args]
        expr = Mul.fromiter(args)
        return self._check_add_Sum(expr, index_symbols)


class TensorElement(TensExpr):
    """
    Tensor with evaluated components.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensorhead
    >>> from sympy import symbols
    >>> L = TensorIndexType("L")
    >>> i, j, k = symbols("i j k")
    >>> A = tensorhead("A", [L, L], [[1], [1]])
    >>> A(i, j).get_free_indices()
    [i, j]

    If we want to set component ``i`` to a specific value, use the
    ``TensorElement`` class:

    >>> from sympy.tensor.tensor import TensorElement
    >>> te = TensorElement(A(i, j), {i: 2})

    As index ``i`` has been accessed (``{i: 2}`` is the evaluation of its 3rd
    element), the free indices will only contain ``j``:

    >>> te.get_free_indices()
    [j]
    """

    def __new__(cls, expr, index_map):
        if not isinstance(expr, Tensor):
            # remap
            if not isinstance(expr, TensExpr):
                raise TypeError("%s is not a tensor expression" % expr)
            return expr.func(*[TensorElement(arg, index_map) for arg in expr.args])
        expr_free_indices = expr.get_free_indices()
        name_translation = {i.args[0]: i for i in expr_free_indices}
        index_map = {name_translation.get(index, index): value for index, value in index_map.items()}
        index_map = {index: value for index, value in index_map.items() if index in expr_free_indices}
        if len(index_map) == 0:
            return expr
        free_indices = [i for i in expr_free_indices if i not in index_map.keys()]
        index_map = Dict(index_map)
        obj = TensExpr.__new__(cls, expr, index_map)
        obj._free_indices = free_indices
        return obj

    @property
    def free(self):
        return [(index, i) for i, index in enumerate(self.get_free_indices())]

    @property
    def dum(self):
        # TODO: inherit dummies from expr
        return []

    @property
    def expr(self):
        return self._args[0]

    @property
    def index_map(self):
        return self._args[1]

    def get_free_indices(self):
        return self._free_indices

    def get_indices(self):
        return self.get_free_indices()

    def _extract_data(self, replacement_dict):
        ret_indices, array = self.expr._extract_data(replacement_dict)
        index_map = self.index_map
        slice_tuple = tuple(index_map.get(i, slice(None)) for i in ret_indices)
        ret_indices = [i for i in ret_indices if i not in index_map]
        array = array.__getitem__(slice_tuple)
        return ret_indices, array


def canon_bp(p):
    """
    Butler-Portugal canonicalization
    """
    if isinstance(p, TensExpr):
        return p.canon_bp()
    return p

def tensor_mul(*a):
    """
    product of tensors
    """
    if not a:
        return TensMul.from_data(S.One, [], [], [])
    t = a[0]
    for tx in a[1:]:
        t = t*tx
    return t


def riemann_cyclic_replace(t_r):
    """
    replace Riemann tensor with an equivalent expression

    ``R(m,n,p,q) -> 2/3*R(m,n,p,q) - 1/3*R(m,q,n,p) + 1/3*R(m,p,n,q)``

    """
    free = sorted(t_r.free, key=lambda x: x[1])
    m, n, p, q = [x[0] for x in free]
    t0 = S(2)/3*t_r
    t1 = - S(1)/3*t_r.substitute_indices((m,m),(n,q),(p,n),(q,p))
    t2 = S(1)/3*t_r.substitute_indices((m,m),(n,p),(p,n),(q,q))
    t3 = t0 + t1 + t2
    return t3

def riemann_cyclic(t2):
    """
    replace each Riemann tensor with an equivalent expression
    satisfying the cyclic identity.

    This trick is discussed in the reference guide to Cadabra.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead, riemann_cyclic
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
    >>> R = tensorhead('R', [Lorentz]*4, [[2, 2]])
    >>> t = R(i,j,k,l)*(R(-i,-j,-k,-l) - 2*R(-i,-k,-j,-l))
    >>> riemann_cyclic(t)
    0
    """
    t2 = t2.expand()
    if isinstance(t2, (TensMul, Tensor)):
        args = [t2]
    else:
        args = t2.args
    a1 = [x.split() for x in args]
    a2 = [[riemann_cyclic_replace(tx) for tx in y] for y in a1]
    a3 = [tensor_mul(*v) for v in a2]
    t3 = TensAdd(*a3).doit()
    if not t3:
        return t3
    else:
        return canon_bp(t3)


def get_lines(ex, index_type):
    """
    returns ``(lines, traces, rest)`` for an index type,
    where ``lines`` is the list of list of positions of a matrix line,
    ``traces`` is the list of list of traced matrix lines,
    ``rest`` is the rest of the elements ot the tensor.
    """
    def _join_lines(a):
        i = 0
        while i < len(a):
            x = a[i]
            xend = x[-1]
            xstart = x[0]
            hit = True
            while hit:
                hit = False
                for j in range(i + 1, len(a)):
                    if j >= len(a):
                        break
                    if a[j][0] == xend:
                        hit = True
                        x.extend(a[j][1:])
                        xend = x[-1]
                        a.pop(j)
                        continue
                    if a[j][0] == xstart:
                        hit = True
                        a[i] = reversed(a[j][1:]) + x
                        x = a[i]
                        xstart = a[i][0]
                        a.pop(j)
                        continue
                    if a[j][-1] == xend:
                        hit = True
                        x.extend(reversed(a[j][:-1]))
                        xend = x[-1]
                        a.pop(j)
                        continue
                    if a[j][-1] == xstart:
                        hit = True
                        a[i] = a[j][:-1] + x
                        x = a[i]
                        xstart = x[0]
                        a.pop(j)
                        continue
            i += 1
        return a

    arguments = ex.args
    dt = {}
    for c in ex.args:
        if not isinstance(c, TensExpr):
            continue
        if c in dt:
            continue
        index_types = c.index_types
        a = []
        for i in range(len(index_types)):
            if index_types[i] is index_type:
                a.append(i)
        if len(a) > 2:
            raise ValueError('at most two indices of type %s allowed' % index_type)
        if len(a) == 2:
            dt[c] = a
    #dum = ex.dum
    lines = []
    traces = []
    traces1 = []
    #indices_to_args_pos = ex._get_indices_to_args_pos()
    # TODO: add a dum_to_components_map ?
    for p0, p1, c0, c1 in ex.dum_in_args:
        if arguments[c0] not in dt:
            continue
        if c0 == c1:
            traces.append([c0])
            continue
        ta0 = dt[arguments[c0]]
        ta1 = dt[arguments[c1]]
        if p0 not in ta0:
            continue
        if ta0.index(p0) == ta1.index(p1):
            # case gamma(i,s0,-s1) in c0, gamma(j,-s0,s2) in c1;
            # to deal with this case one could add to the position
            # a flag for transposition;
            # one could write [(c0, False), (c1, True)]
            raise NotImplementedError
        # if p0 == ta0[1] then G in pos c0 is mult on the right by G in c1
        # if p0 == ta0[0] then G in pos c1 is mult on the right by G in c0
        ta0 = dt[arguments[c0]]
        b0, b1 = (c0, c1) if p0 == ta0[1]  else (c1, c0)
        lines1 = lines[:]
        for line in lines:
            if line[-1] == b0:
                if line[0] == b1:
                    n = line.index(min(line))
                    traces1.append(line)
                    traces.append(line[n:] + line[:n])
                else:
                    line.append(b1)
                break
            elif line[0] == b1:
                line.insert(0, b0)
                break
        else:
            lines1.append([b0, b1])

        lines = [x for x in lines1 if x not in traces1]
        lines = _join_lines(lines)
    rest = []
    for line in lines:
        for y in line:
            rest.append(y)
    for line in traces:
        for y in line:
            rest.append(y)
    rest = [x for x in range(len(arguments)) if x not in rest]

    return lines, traces, rest


def get_free_indices(t):
    if not isinstance(t, TensExpr):
        return ()
    return t.get_free_indices()


def get_indices(t):
    if not isinstance(t, TensExpr):
        return ()
    return t.get_indices()


def get_index_structure(t):
    if isinstance(t, TensExpr):
        return t._index_structure
    return _IndexStructure([], [], [], [])


def get_coeff(t):
    if isinstance(t, Tensor):
        return S.One
    if isinstance(t, TensMul):
        return t.coeff
    if isinstance(t, TensExpr):
        raise ValueError("no coefficient associated to this tensor expression")
    return t

def contract_metric(t, g):
    if isinstance(t, TensExpr):
        return t.contract_metric(g)
    return t


def perm2tensor(t, g, is_canon_bp=False):
    """
    Returns the tensor corresponding to the permutation ``g``

    For further details, see the method in ``TIDS`` with the same name.
    """
    if not isinstance(t, TensExpr):
        return t
    elif isinstance(t, (Tensor, TensMul)):
        nim = get_index_structure(t).perm2tensor(g, is_canon_bp=is_canon_bp)
        res = t._set_new_index_structure(nim, is_canon_bp=is_canon_bp)
        if g[-1] != len(g) - 1:
            return -res

        return res
    raise NotImplementedError()


def substitute_indices(t, *index_tuples):
    """
    Return a tensor with free indices substituted according to ``index_tuples``

    ``index_types`` list of tuples ``(old_index, new_index)``

    Note: this method will neither raise or lower the indices, it will just replace their symbol.

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, tensorhead
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
    >>> A, B = tensorhead('A,B', [Lorentz]*2, [[1]*2])
    >>> t = A(i, k)*B(-k, -j); t
    A(i, L_0)*B(-L_0, -j)
    >>> t.substitute_indices((i,j), (j, k))
    A(j, L_0)*B(-L_0, -k)
    """
    if not isinstance(t, TensExpr):
        return t
    free = t.free
    free1 = []
    for j, ipos in free:
        for i, v in index_tuples:
            if i._name == j._name and i.tensor_index_type == j.tensor_index_type:
                if i._is_up == j._is_up:
                    free1.append((v, ipos))
                else:
                    free1.append((-v, ipos))
                break
        else:
            free1.append((j, ipos))

    t = TensMul.from_data(t.coeff, t.components, free1, t.dum)
    return t


def _expand(expr, **kwargs):
    if isinstance(expr, TensExpr):
        return expr._expand(**kwargs)
    else:
        return expr.expand(**kwargs)


class TensorBinaryCondition(Boolean):
    """Base class for all binary relation types.
    """
    __slots__ = ()
    
    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> TensorEqual(x, 1)
        TensorEqual(x, 1)
        >>> _.reversed
        TensorEqual(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, evaluate=False)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        return self.lhs.domain_defined(x) & self.rhs.domain_defined(x)

    def domain_definition(self, **_):
        return self.lhs.domain_definition() & self.rhs.domain_definition()
    
    def __bool__(self):
        return False
    
    @staticmethod
    def eval(cls, *args, **options):
        args = list(map(sympify, args))
        from sympy.core.parameters import global_parameters
        if options.pop('evaluate', global_parameters.evaluate):
            evaluated = cls.eval(*args)
            if evaluated is not None:

                if options and evaluated.is_BooleanAtom and 'plausible' in options:
                    if evaluated:
                        options['plausible'] = None
                    else:
                        options['plausible'] = False
                else:
                    return evaluated.copy(**options)
                
        if options:
            from sympy.core.inference import Inference
            return Inference(TensorBinaryCondition.__new__(cls, *args), **options)            
                
        return TensorBinaryCondition.__new__(cls, *args, **options)
    
    @property
    def wrt(self):
        free_symbols = self.lhs.free_symbols
        if not free_symbols:
            free_symbols = self.rhs.free_symbols
        return next(iter(free_symbols))
    
    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res
        
        old, new = args
        if old.is_Sliced:
            return self._subs_sliced(old, new)
        if not old.is_symbol:
            return self
        
        new = sympify(new)
        domain = old.domain_bounded
        if domain is not None and new not in domain:
            return self

        return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify())

    @cacheit
    def _eval_shape(self):
        return self.lhs.shape
    
    def __iter__(self):
        raise
        
    def __getitem__(self, indices):
        lhs, rhs = self.lhs[indices], self.rhs[indices]
        if lhs.shape:
            return self.func(lhs, rhs, evaluate=False)
        return self.scalar_operator(lhs, rhs, evaluate=False)
            
# from sympy.logic.boolalg import Boolean
class TensorRelational(TensorBinaryCondition, Expr):
    """Base class for all tensor-relation types.

    Explanation
    ===========

    Subclasses of TensorRelational should generally be instantiated directly, but
    TensorRelational can be instantiated with a valid ``rop`` value to dispatch to
    the appropriate subclass.

    Parameters
    ==========

    rop : str or None
        Indicates what subclass to instantiate.  Valid values can be found
        in the keys of TensorRelational.ValidRelationOperator.

    """
    __slots__ = ()

    ValidRelationOperator = {}  # type: Dict[Union[str, None], Type[TensorRelational]]

    _op_priority = 12  # higher than Expr
    # ValidRelationOperator - Defined below, because the necessary classes
    #   have not yet been defined

    def __new__(cls, lhs, rhs, rop=None, **assumptions):

        # If called by a subclass, do nothing special and pass on to Expr.

        if cls is not TensorRelational:
            return TensorBinaryCondition.__new__(cls, lhs, rhs, **assumptions)
        # If called directly with an operator, look up the subclass
        # corresponding to that operator and delegate to it
        try:
            cls = cls.ValidRelationOperator[rop]
            rv = cls(lhs, rhs, **assumptions)
            # /// drop when Py2 is no longer supported
            # validate that Booleans are not being used in a relational
            # other than Eq/Ne;
            if isinstance(rv, (TensorEqual, TensorUnequal)):
                pass
            elif isinstance(rv, TensorRelational):  # could it be otherwise?
                for a in rv.args:
                    if isinstance(a, Symbol):
                        continue
                    if isinstance(a, Boolean):
                        from sympy.utilities.misc import filldedent
                        raise TypeError(filldedent('''
                            A Boolean argument can only be used in
                            Eq and Ne; all other relationals expect
                            real expressions.
                        '''))
            # \\\
            return rv
        except KeyError:
            raise ValueError(
                "Invalid relational operator symbol: %r" % rop)

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> TensorEqual(x, 1)
        TensorEqual(x, 1)
        >>> _.reversed
        TensorEqual(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, evaluate=False)

    def __neg__(self):
        """Return the relationship with signs reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> TensorEqual(x, 1)
        TensorEqual(x, 1)
        >>> -_
        TensorEqual(-x, -1)
        >>> x < 1
        x < 1
        >>> -_
        -x > -1
        """

        lhs, rhs = -self.lhs, -self.rhs
        lhs, rhs = lhs.simplify(), rhs.simplify()
        return self.reversed_type(lhs, rhs)

    def _eval_evalf(self, prec):
        return self.func(*[s._evalf(prec) for s in self.args])

    @property
    def canonical(self):
        """Return a canonical form of the relational by putting a
        number on the rhs, canonically removing a sign or else
        ordering the args canonically. No other simplification is
        attempted.

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> x < 2
        x < 2
        >>> _.reversed.canonical
        x < 2
        >>> (-y < x).canonical
        x > -y
        >>> (-y > x).canonical
        x < -y
        >>> (-y < -x).canonical
        x < y
        """
        args = self.args
        r = self
        if r.rhs.is_number:
            if r.rhs.is_Number and r.lhs.is_Number and r.lhs > r.rhs:
                r = r.reversed
        elif r.lhs.is_number:
            r = r.reversed
        elif tuple(ordered(args)) != args:
            r = r.reversed

        # Check if first value has negative sign
        if not isinstance(r.lhs, BooleanAtom) and \
                r.lhs.could_extract_minus_sign():
            r = -r
        elif not isinstance(r.rhs, BooleanAtom) and not r.rhs.is_number and \
                r.rhs.could_extract_minus_sign():
            # Right hand side has a minus, but not lhs.
            # How does the expression with reversed signs behave?
            # This is so that expressions of the type TensorEqual(x, -y) and TensorEqual(-x, y)
            # have the same canonical representation
            expr1, _ = ordered([r.lhs, -r.rhs])
            if expr1 != r.lhs:
                r = -r.reversed
        return r

    def equals(self, other, failing_expression=False):
        """Return True if the sides of the relationship are mathematically
        identical and the type of relationship is the same.
        If failing_expression is True, return the expression whose truth value
        was unknown."""
        if isinstance(other, TensorRelational):
            if self == other or self.reversed == other:
                return True
            a, b = self, other
            if a.func in (TensorEqual, TensorUnequal) or b.func in (TensorEqual, TensorUnequal):
                if a.func != b.func:
                    return False
                left, right = [i.equals(j,
                                        failing_expression=failing_expression)
                               for i, j in zip(a.args, b.args)]
                if left is True:
                    return right
                if right is True:
                    return left
                lr, rl = [i.equals(j, failing_expression=failing_expression)
                          for i, j in zip(a.args, b.reversed.args)]
                if lr is True:
                    return rl
                if rl is True:
                    return lr
                e = (left, right, lr, rl)
                if all(i is False for i in e):
                    return False
                for i in e:
                    if i not in (True, False):
                        return i
            else:
                if b.func != a.func:
                    b = b.reversed
                if a.func != b.func:
                    return False
                left = a.lhs.equals(b.lhs,
                                    failing_expression=failing_expression)
                if left is False:
                    return False
                right = a.rhs.equals(b.rhs,
                                     failing_expression=failing_expression)
                if right is False:
                    return False
                if left is True:
                    return right
                return left

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify import simplify
        r = self
        r = r.func(*[simplify(i, ratio=ratio, measure=measure, rational=rational, inverse=inverse) for i in r.args])
        if r.is_Relational:
            dif = r.lhs - r.rhs
            # replace dif with a valid Number that will
            # allow a definitive comparison with 0
            v = None
            if dif.is_comparable:
                v = dif.n(2)
            elif dif.equals(0):  # XXX this is expensive
                v = S.Zero
            if v is not None:
                r = r.func._eval_relation(v, S.Zero)

        r = r.canonical
        if measure(r) < ratio * measure(self):
            return r
        else:
            return self

    def _eval_trigsimp(self, **opts):
        from sympy.simplify import trigsimp
        return self.func(trigsimp(self.lhs, **opts), trigsimp(self.rhs, **opts))

    def expand(self, *args, **kwargs):
        return self.func(self.lhs.expand(*args, **kwargs), self.rhs.expand(*args, **kwargs))

    def _eval_as_set(self):
        # self is univariate and periodicity(self, x) in (0, None)
        from sympy.solvers.inequalities import solve_univariate_inequality
        syms = self.free_symbols
        assert len(syms) == 1
        x, = syms
        return solve_univariate_inequality(self, x, relational=False)

    @property
    def binary_symbols(self):
        # override where necessary
        return set()

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return TensorBinaryCondition.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Relational(self, lhs, rhs)
        if this is not None:
            return this
        
        return self

    def doit(self, *args, **kwargs):
        return self.func(self.lhs.doit(*args, **kwargs), self.rhs.doit(*args, **kwargs))

    def __add__(self, other):
        other = sympify(other)
        if isinstance(other, TensorEqual):
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif isinstance(other, TensorRelational):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        elif other.is_Quantifier:
            return self.bfn(self.__add__, other)
        else:
            assert other.is_complex, 'try to prove %s is complex' % other
            return self.func(self.lhs + other, self.rhs + other)

    def __sub__(self, other):
        other = sympify(other)
        if other.is_Equal: 
            return self.func(self.lhs - other.lhs, self.rhs - other.rhs, **other.add_sub_assumptions(self))
        elif other.is_Quantifier:
            return self.bfn(self.__sub__, other)
        else: 
            assert not other.is_set
            assert other.is_complex, 'try to prove %s is complex' % other
            return self.func((self.lhs - other).simplify(), (self.rhs - other).simplify())

    def __mul__(self, other):
        if isinstance(other, TensorEqual):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs * other.lhs, self.rhs * other.rhs)
            return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        else:
            other = sympify(other)
            if other.is_extended_positive:
                return self.func(self.lhs * other, self.rhs * other)
            if other.is_extended_negative:
                return self.reversed_type(self.lhs * other, self.rhs * other)
            elif other.is_extended_nonnegative:
                return self.func(self.lhs * other, self.rhs * other, given=self)
            elif other.is_extended_nonpositive:
                return self.reversed_type(self.lhs * other, self.rhs * other, given=self)
            return self

    def __truediv__(self, other):
        if isinstance(other, TensorEqual):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs / other.lhs, self.rhs / other.rhs)
            return self
        else:
            other = sympify(other)
            if other.is_extended_positive:
                return self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            if other.is_extended_negative:
                return self.reversed_type((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            return self

    def __iter__(self):
        raise TypeError

    def is_positive_relationship(self):
        ...

    def _sympystr(self, p):
        return self.func.__name__[6:] + "(%s)" % p.stringify(self.args, ", ")

    def _lean(self, p):
        return self.func.__name__[6:] + "(%s)" % p.stringify(self.args, ", ")

    def _latex(self, p, exp=None):
        func = self.func.__name__[6:]
        args = [str(p._print(arg)) for arg in self.args]
        if exp is not None:
            name = r'%s^{%s}' % (p._hprint_Function(func), exp)
        else:
            name = p._hprint_Function(func)

        name += r"{\left(%s \right)}"

        return name % ",".join(args)

    def domain_conditioned(self, var):
        from sympy.sets.sets import FiniteSet
        domain = var.domain & self.domain_defined(var)
        if var.shape or var.is_set:
            return TensorBinaryCondition.domain_conditioned(self, var)
        
        equation = self.lhs - self.rhs
        
        p = equation.as_poly(var)
        if not p or p.degree() != 1:
            return TensorBinaryCondition.domain_conditioned(self, var)
         
        a = p.nth(1)
        if a.is_nonzero:
            b = p.nth(0)
            solution = -b / a
            op = type(self)
            if a.is_extended_negative:
                a = -a
                dic = {TensorEqual: TensorEqual, TensorGreater: TensorLess, TensorGreaterEqual: TensorLessEqual, TensorLess: TensorGreater, TensorLessEqual: TensorGreaterEqual, TensorUnequal: TensorUnequal}
                op = dic[op]
                            
            from sympy import Interval
            if op == TensorLessEqual:
                domain &= Interval(S.NegativeInfinity, solution)
            elif op == TensorGreaterEqual:
                domain &= Interval(solution, S.Infinity)
            elif op == TensorLess:
                domain &= Interval(S.NegativeInfinity, solution, right_open=True)
            elif op == TensorGreater:
                domain &= Interval(solution, S.Infinity, left_open=True)
            elif op == TensorUnequal:
                domain -= FiniteSet(solution)
            elif op == TensorEqual:
                domain &= FiniteSet(solution)

        return domain

    @cacheit
    def _eval_domain_defined(self, x, **_):
        return self.lhs.domain_defined(x, real=True) & self.rhs.domain_defined(x, real=True)

    def invert(self):
        lhs, rhs = self.args
        
        if len(lhs.shape) < len(rhs.shape):
            shape = rhs.shape
        else:
            shape = lhs.shape

        if shape:
            excludes = set()
            indices = []
            limits = []
            for n in shape:
                i = self.generate_var(excludes, integer=True)
                excludes.add(i)
                indices.append(i)
                limits.append((i, 0, n))
                
            indices = tuple(indices)
            
            if len(lhs.shape) < len(rhs.shape):
                lhs_indices = indices[len(rhs.shape) - len(lhs.shape):]
                if lhs_indices:
                    lhs = lhs[lhs_indices]
                rhs = rhs[indices]                
            elif len(lhs.shape) > len(rhs.shape):
                rhs_indices = indices[len(lhs.shape) - len(rhs.shape):]
                if rhs_indices:
                    rhs = rhs[rhs_indices]
                lhs = lhs[indices]
            else:
                lhs, rhs = lhs[indices], rhs[indices]
            
            eq = Boolean.__new__(self.invert_type, lhs, rhs)
            from sympy.concrete.exists import Any
            return Any(eq, *limits[::-1])
        
        return TensorBinaryCondition.invert(self)
                    
                    
class TensorEqual(TensorRelational):
    """An equal relation between two objects.

    Explanation
    ===========

    Represents that two objects are equal.  If they can be easily shown
    to be definitively equal (or unequal), this will reduce to True (or
    False).  Otherwise, the relation is maintained as an unevaluated
    TensorEqual object.  Use the ``simplify`` function on this object for
    more nontrivial evaluation of the equality relation.

    As usual, the keyword argument ``evaluate=False`` can be used to
    prevent any evaluation.
    """
    rel_op = '=='
    scalar_operator = Equal
    __slots__ = ()

    def __new__(cls, lhs, rhs=None, **options):

        evaluate = options.pop('evaluate', global_parameters.evaluate)
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)
        if evaluate:
            # If one expression has an _eval_Eq, return its results.
            if hasattr(lhs, '_eval_Eq'):
                r = lhs._eval_Eq(rhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            if hasattr(rhs, '_eval_Eq'):
                r = rhs._eval_Eq(lhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            # If expressions have the same structure, they must be equal.
            if lhs == rhs or lhs.dummy_eq(rhs):
                return S.true.copy(**options)  # e.g. True == True
            elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
                return S.false  # True != False
            elif not (lhs.is_Symbol or rhs.is_Symbol) and (lhs.is_Boolean != rhs.is_Boolean):
                return S.false  # only Booleans can equal Booleans
            from sympy.sets.contains import Element
            if Element(rhs, lhs.domain).is_BooleanFalse or Element(lhs, rhs.domain).is_BooleanFalse:
                return S.false.copy(**options)

            if isinstance(lhs, Expr) and isinstance(rhs, Expr) and not lhs.dtype.is_set and not rhs.dtype.is_set and not lhs.dtype.is_bool:
                # see if the difference evaluates
                if lhs.is_infinite:
                    if rhs.is_infinite:
                        if lhs == rhs:
                            return S.true.copy(**options)
                        else:
                            return S.false.copy(**options)
                    else:  
                        ...
                else:
                    if rhs.is_infinite:
                        ...
                    else:                       
                        dif = (lhs - rhs).simplify()
                        z = dif.is_zero
                        if z is not None:
                            if z is False:
                                return S.false.copy(**options)
                            if z:
                                if 'plausible' in options:
                                    del options['plausible']
                                else:
                                    return S.true.copy(**options)
        if options:
            from sympy.core.inference import Inference
            return Inference(TensorRelational.__new__(cls, lhs, rhs), **options)

        return TensorRelational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs == rhs)

    def _eval_rewrite_as_Add(self, *args, **kwargs):
        """
        return TensorEqual(L, R) as L - R. To control the evaluation of
        the result set pass `evaluate=True` to give L - R;
        if `evaluate=None` then terms in L and R will not cancel
        but they will be listed in canonical order; otherwise
        non-canonical args will be returned.

        Examples
        ========

        >>> from sympy import Eq, Add
        >>> from sympy.abc import b, x
        >>> eq = TensorEqual(x + b, x - b)
        >>> eq.rewrite(Add)
        2*b
        >>> eq.rewrite(Add, evaluate=None).args
        (b, b, x, -x)
        >>> eq.rewrite(Add, evaluate=False).args
        (b, x, b, -x)
        """
        from .add import _unevaluated_Add, Add
        L, R = args
        evaluate = kwargs.get('evaluate', True)
        if evaluate:
            # allow cancellation of args
            return L - R
        args = Add.make_args(L) + Add.make_args(-R)
        if evaluate is None:
            # no cancellation, but canonical
            return _unevaluated_Add(*args)
        # no cancellation, not canonical
        return Add._from_args(args)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        e = super()._eval_simplify(**kwargs)
        if not isinstance(e, TensorEqual):
            return e
        free = self.free_symbols
        if len(free) == 1:
            try:
                x, = free
                m, b = linear_coeffs(
                    e.rewrite(Add, evaluate=False), x)
                if m.is_zero == False:
                    enew = e.func(x, -b / m)
                else:
                    enew = e.func(m * x, -b)
                measure = kwargs['measure']
                if measure(enew) <= kwargs['ratio'] * measure(e):
                    e = enew
            except ValueError:
                pass
        return e.canonical

    def __truediv__(self, other):
        other = sympify(other)
        if other.is_Equal:
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func((self.lhs / other.lhs).ratsimp(), (self.rhs / other.rhs).ratsimp())
            return self
        else:
            lhs = (self.lhs / other).ratsimp().simplify()
            rhs = (self.rhs / other).ratsimp().simplify()
            if other.is_nonzero:
                return self.func(lhs, rhs)
            from sympy import Or
            return Or(self.func(other, 0), self.func(lhs, rhs))

    def __rmul__(self, lhs):
        return self.__mul__(lhs)
        
    def __mod__(self, other):
        other = sympify(other)
        assert other.is_integer
        return TensorEqual(self.lhs % other, self.rhs % other, given=self)
     
    def __mul__(self, other):
        other = sympify(other)
        if isinstance(other, TensorEqual):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs)
            return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

        elif isinstance(other, TensorLess):
            if other.lhs.is_extended_positive:
                return TensorLess(self.lhs * other.lhs, self.rhs * other.rhs)
            elif other.lhs.is_extended_nonnegative:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs)
                return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=self)

            elif other.rhs.is_extended_negative:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs)
                return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

            elif other.rhs.is_extended_nonpositive:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs)
                return TensorEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

            return self
        else:
            if other.is_nonzero:
                return TensorEqual(self.lhs * other, self.rhs * other)
            return TensorEqual(self.lhs * other, self.rhs * other, given=self)

    def __rmatmul__(self, lhs):
        if isinstance(lhs, TensorEqual):
            if lhs.lhs.is_invertible or lhs.rhs.is_invertible:
                return TensorEqual(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs)
            return TensorEqual(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=[self, lhs])
        else:
            if lhs.is_invertible:
                return TensorEqual(lhs @ self.lhs, lhs @ self.rhs, equivalent=self)
            return TensorEqual(lhs @ self.lhs, lhs @ self.rhs, given=self)

    def __matmul__(self, rhs):
        if isinstance(rhs, TensorEqual):
            if rhs.lhs.is_invertible or rhs.rhs.is_invertible:
                return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs)
            return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, given=[self, rhs])

        else: 
            if rhs.is_invertible:
                return self.func(self.lhs @ rhs, self.rhs @ rhs, equivalent=self)
            return self.func(self.lhs @ rhs, self.rhs @ rhs, given=self)

    def __rpow__(self, other):
        if other.is_positive:
            return self.func(other ** self.lhs, other ** self.rhs)
        
        if self.lhs.is_positive or self.rhs.is_positive:
            return self.func(other ** self.lhs, other ** self.rhs, given=self)
        
        return self

    def __pow__(self, other):
        other = sympify(other)
        if other.is_positive:
            return self.func(self.lhs ** other, self.rhs ** other, given=self)
        return self
        
    def powsimp(self, *args, **kwargs):
        return TensorEqual(self.lhs.powsimp(*args, **kwargs), self.rhs.powsimp(*args, **kwargs))

    def collect(self, syms):
        return TensorEqual(self.lhs.collect(syms), self.rhs.collect(syms))

    def rsolve(self, y):
        from sympy.solvers.recurr import rsolve
        solution = rsolve(self, y, symbols=True)
        if solution is None:
            return self
        solution, limits = solution
        
        eq = self.func(y, solution)
        if len(limits) == 0:
            eq.equivalent = self
            return eq
        from sympy import Any
        for i, C in enumerate(limits):
            limits[i] = (C,)
        return Any(eq, *limits)

    def solve(self, x):
        from sympy.solvers.solvers import solve
        res = solve(self.lhs - self.rhs, x)

        if len(res) == 1:
            x_sol, *_ = res
            return TensorEqual(x, x_sol)
        if len(res) > 1:
            from sympy.logic.boolalg import Or
            return Or(*(self.func(x, x_sol) for x_sol in res))

        return self

    def subs(self, *args, simplify=True, **kwargs):
        [*args] = map(sympify, args)
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, dict):
                if 'simultaneous' in kwargs:
                    if self.plausible:
                        return self
                    return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify()).simplify()
                else:
                    subs = self
                    for key, value in arg.items():
                        subs = subs.subs(key, value)
                    return subs
            elif isinstance(arg, TensorEqual):
                eq = arg
                args = eq.args
                
                lhs = self.lhs._subs(*args, simplify=simplify, **kwargs)
                rhs = self.rhs._subs(*args, simplify=simplify, **kwargs)
                
                if simplify:
                    lhs = lhs.simplify()
                    rhs = rhs.simplify()
                if lhs == self.lhs and rhs == self.rhs:
                    return self
                
                result = self.func(lhs, rhs)
                return self.subs_assumptions_for_equality(eq, result, simplify=simplify)
            elif arg.is_Quantifier:
                return self.bfn(self.subs, arg)
            else:
                return self

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return TensorBinaryCondition.subs(self, *args, **kwargs)

    def combsimp(self, *args):
        from sympy import combsimp
        return self.func(combsimp(self.lhs, *args), combsimp(self.rhs, *args))

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return TensorBinaryCondition.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Equal(self, lhs, rhs)
        if this is not None:
            return this
        
        this = self.rhs.func.simplify_Equal(self, rhs, lhs)
        if this is not None:
            return this
        
        return self

    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        limits_dict = self.limits_dict
        x = None
        if self.expr.lhs in limits_dict:
            x = self.expr.lhs
            y = self.expr.rhs
        elif self.expr.rhs in limits_dict:
            x = self.expr.rhs
            y = self.expr.lhs

        if x is not None and not y._has(x):
            domain = limits_dict[x]
            if isinstance(domain, Boolean):
                function = domain._subs(x, y)
                if function == False:
                    function = self.limits_cond.invert()
                    return function

    def simplify_Intersection(self, lhs):
        if len(lhs.args) == 2:
            A, B = lhs.args
            if A.is_FiniteSet and B.is_FiniteSet:
                if len(A) == len(B) == 1:
                    return TensorUnequal(A.arg, B.arg)
        
    @property
    def T(self):
        return self.func(self.lhs.T, self.rhs.T)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Equal:
            if self.lhs == other.rhs:
                eq = TensorEqual(self.rhs, other.lhs)
                if eq:
                    return self
                if eq == False:
                    return S.false
                
            elif self.lhs == other.lhs:
                eq = TensorEqual(self.rhs, other.rhs)
                if eq:
                    return self
                if eq == False:
                    return S.false
                
        elif isinstance(other, (TensorLess, TensorGreater)):
            if set(self.args) == set(other.args):
                return S.false
        elif other.is_GreaterEqual or other.is_LessEqual:
            if set(self.args) == set(other.args):
                return self
        elif other.is_NotElement:
            if self.lhs == other.lhs:
                if self.rhs in other.rhs:
                    return S.false
            elif self.rhs == other.lhs:
                if self.lhs in other.rhs:
                    return S.false
        elif other.is_Element:
            from sympy import Element
            if self.lhs == other.lhs: 
                if Element(self.rhs, other.rhs).is_BooleanFalse:
                    return S.false
            elif self.rhs == other.lhs:
                if Element(self.lhs, other.rhs).is_BooleanFalse:
                    return S.false
        return TensorRelational.__and__(self, other)

    def add_sub_assumptions(self, other):
        kwargs = {}
        if other.lhs.is_set:
            if self.plausible is None:
                if other.plausible is None:
                    kwargs['equivalent'] = self
                else:
                    kwargs['given'] = other
            else:
                kwargs['given'] = [self, other]
        else:
            if other.plausible is None:
                if other.is_Equal or self.plausible is None:
                    kwargs['equivalent'] = self
                else:
                    kwargs['given'] = self
            elif self.plausible is None:
                kwargs['equivalent'] = other
            else:
                kwargs['given'] = [self, other]
        return kwargs
        
    def __add__(self, other):
        if isinstance(other, TensorRelational):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, **self.add_sub_assumptions(other)).simplify()
        return TensorRelational.__add__(self, other)
        
    def __rsub__(self, other):
        other = sympify(other)
        assert not isinstance(other, TensorRelational) 
        return self.func(other - self.lhs, other - self.rhs).simplify()
     
    def __sub__(self, other):
        if isinstance(other, TensorRelational): 
            return other.reversed_type((self.lhs - other.lhs).simplify(), (self.rhs - other.rhs).simplify(), **self.add_sub_assumptions(other)).simplify()
        return TensorRelational.__sub__(self, other)

    def __or__(self, other):
        if other.is_Greater:
            if {*other.args} == {*self.args}:
                return TensorGreaterEqual(*other.args)
        elif other.is_Less:
            if {*other.args} == {*self.args}:
                return TensorLessEqual(*other.args)
        elif other.is_LessEqual:
            if {*other.args} == {*self.args}:
                return other
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs == other.rhs + 1:
#                 x == 3 and x <= 2 => x <= 3
                return TensorLessEqual(*self.args)
        elif other.is_GreaterEqual:
            if {*other.args} == {*self.args}:
                return other
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs + 1 == other.rhs:
#                 x == 3 and x >= 2 => x >= 3
                return TensorGreaterEqual(*self.args)
            
        return TensorRelational.__or__(self, other)

    def simplify_condition_on_random_variable(self):
        lhs, rhs = self.args
        from sympy.stats.rv import pspace
        if lhs.is_symbol and pspace(lhs).symbol == rhs:
            return lhs
        return self

    def domain_conditioned(self, var):
        if var.shape:
            if self.lhs == var:
                return self.rhs.set
            
            if self.rhs == var:
                return self.lhs.set
            
            return TensorBinaryCondition.domain_conditioned(self, var)
        if not self.lhs.is_set and not var.is_set:
            return TensorRelational.domain_conditioned(self, var)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Equal and len(cls.args) == 2:
                a, b = cls.args
                cls = Basic.__new__(TensorEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number or b.is_EmptySet:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
        elif isinstance(res, tuple):
            if cls.is_Equal:
                args = cls.args
                if isinstance(args, tuple) and len(args) == 1:
                    _a, _b = res
                    a, b = self.args
                    if a is _a:
                        return (_b, _a)
            
        return res

    invert = TensorBinaryCondition.invert
    
eq = TensorEqual


class TensorUnequal(TensorRelational):
    """An unequal relation between two objects.

    Explanation
    ===========

    Represents that two objects are not equal.  If they can be shown to be
    definitively equal, this will reduce to False; if definitively unequal,
    this will reduce to True.  Otherwise, the relation is maintained as an
    TensorUnequal object.

    Examples
    ========

    >>> from sympy import Ne
    >>> from sympy.abc import x, y
    >>> Ne(y, x+x**2)
    Ne(y, x**2 + x)

    See Also
    ========
    TensorEqual

    Notes
    =====
    This class is not the same as the != operator.  The != operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    This class is effectively the inverse of TensorEqual.  As such, it uses the
    same algorithms, including any available `_eval_Eq` methods.

    """
    rel_op = '!='

    scalar_operator = Unequal
    invert_type = TensorEqual
    __slots__ = ()

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)
        evaluate = options.pop('evaluate', global_parameters.evaluate)
        if evaluate:
            is_equal = TensorEqual(lhs, rhs)
            if isinstance(is_equal, BooleanAtom):
                if 'plausible' in options:
                    if is_equal:
                        options['plausible'] = False
                    else:
                        options['plausible'] = None
                else:
                    return is_equal.invert().copy(**options)

        if options:
            from sympy.core.inference import Inference
            return Inference(TensorRelational.__new__(cls, lhs, rhs), **options)

        return TensorRelational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs != rhs)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        # simplify as an equality
        eq = TensorEqual(*self.args)._eval_simplify(**kwargs)
        if isinstance(eq, TensorEqual):
            # send back Ne with the new args
            return self.func(*eq.args)
        return ~eq  # result of Ne is the negated Eq

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, TensorEqual):
                eq = arg
                args = eq.args
                lhs = self.lhs.subs(*args, **kwargs)
                rhs = self.rhs.subs(*args, **kwargs)
                return self.func(lhs, rhs).simplify().overwrite(self)
            else:
                return self

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return TensorBinaryCondition.subs(self, *args, **kwargs)

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return TensorBinaryCondition.simplify(self, deep=True, wrt=wrt)

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Unequal(self, lhs, rhs)
        if this is not None:
            return this.simplify()
             
        this = self.rhs.func.simplify_Unequal(self, rhs, lhs)
        if this is not None:
            return this
        
        return super(TensorUnequal, self).simplify()

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Or:
            return other.__and__(self)
        if isinstance(other, TensorLessEqual):
            if set(self.args) == set(other.args):
                return TensorLess(other.lhs, other.rhs)

        if isinstance(other, TensorGreaterEqual):
            if set(self.args) == set(other.args):
                return TensorGreater(other.lhs, other.rhs)

        if isinstance(other, (TensorLess, TensorGreater)):
            if set(self.args) == set(other.args):
                return other

        if isinstance(other, TensorEqual):
            argset = {*self.args}
            _argset = {*other.args}
            x = argset & _argset
            if len(x) == 2:
                return S.false
            elif len(x) == 1:
                x, *_ = x
                argset.remove(x)
                _argset.remove(x)
                lhs, *_ = argset
                rhs, *_ = _argset
                eq = TensorEqual(lhs, rhs).simplify()
                if eq.is_BooleanFalse: 
                    return other
                
        return TensorRelational.__and__(self, other)

    def __truediv__(self, other):
        if other.is_Equal:
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs / other.lhs, self.rhs / other.rhs)
            return self
        else:
            if other.is_nonzero:
                return self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            if other.is_zero:
                return self
            from sympy import Or
            return Or(TensorEqual(other, 0), self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp()))

    def __mul__(self, other):
        if isinstance(other, TensorUnequal):
            return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        
        return TensorRelational.__mul__(self, other)

    def __or__(self, other):
        if isinstance(other, TensorLessEqual):
            if self.lhs == other.lhs and self.rhs <= other.rhs or \
            self.lhs == other.rhs and other.rhs <= self.rhs or \
            self.rhs == other.lhs and self.lhs <= other.rhs or \
            self.rhs == other.rhs and other.lhs <= self.rhs:
                return S.true
        elif isinstance(other, TensorGreaterEqual):
            if self.lhs == other.lhs and self.rhs >= other.rhs or \
            self.lhs == other.rhs and other.rhs >= self.rhs or \
            self.rhs == other.lhs and self.lhs >= other.rhs or \
            self.rhs == other.rhs and other.lhs >= self.rhs:
                return S.true
            
        return TensorRelational.__or__(self, other)

    def domain_conditioned(self, var):
        if not self.lhs.is_set: 
            return TensorRelational.domain_conditioned(self, var)
        return TensorBinaryCondition.domain_conditioned(self, var)
    
    of = TensorEqual.of

    invert = TensorBinaryCondition.invert

ne = TensorUnequal
TensorEqual.invert_type = TensorUnequal


class TensorInequality(TensorRelational):
    """Internal base class for all *Than types.

    Each subclass must implement _eval_relation to provide the method for
    comparing two real numbers.

    """
    __slots__ = ()

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        if len(lhs.shape) > len(rhs.shape):
            rhs *= Ones(*lhs.shape)
        elif len(lhs.shape) < len(rhs.shape):
            lhs *= Ones(*rhs.shape)

        evaluate = options.pop('evaluate', global_parameters.evaluate)
        if evaluate:
            ...
        # make a "non-evaluated" Expr for the inequality
        if options:
            from sympy.core.inference import Inference
            return Inference(TensorRelational.__new__(cls, lhs, rhs), **options)
        
        return TensorRelational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs, **options):
        val = cls._eval_fuzzy_relation(lhs, rhs)
        if val is None:
            return cls(lhs, rhs, evaluate=False)
        else:
            return _sympify(val)

    def __and__(self, other):
        if other.is_And:
            eqs = other.args
            for i, eq in enumerate(eqs):
                et = self & eq
                if et.is_And:
                    continue
                
                eqs = [*eqs]
                del eqs[i]
                return et & other.func(*eqs)
                        
        return TensorRelational.__and__(self, other)


class _TensorGreater(TensorInequality):
    """Not intended for general use

    _TensorGreater is only used so that TensorGreaterEqual and TensorGreater may
    subclass it for the .gts and .lts properties.

    """
    __slots__ = ()

    def __and__(self, other):
        if isinstance(other, _TensorGreater): 
            if self.lhs == other.lhs:
                from sympy import Max
                if self.func == other.func:
                    m = Max(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other
                
        elif isinstance(other, _TensorLess):
            if self.rhs == other.rhs: 
                left = other.lhs
                left_open = isinstance(other, TensorLess)
                
                right = self.lhs
                right_open = isinstance(self, TensorGreater)
                if left_open:
                    if right_open:
                        ...
                    else:
                        if left >= right:
                            return S.false
                
        return TensorInequality.__and__(self, other)

    @property
    def gts(self):
        return self._args[0]

    @property
    def lts(self):
        return self._args[1]

    def limit(self, x, xlim, dir=1):
        """ Compute limit x->xlim.
        """
        return TensorGreaterEqual(self.lhs.limit(x, xlim, dir), self.rhs.limit(x, xlim, dir), given=self, evaluate=False)


class _TensorLess(TensorInequality):
    """Not intended for general use.

    _TensorLess is only used so that TensorLessEqual and TensorLess may subclass it for
    the .gts and .lts properties.

    """
    __slots__ = ()

    @property
    def gts(self):
        return self._args[1]

    @property
    def lts(self):
        return self._args[0]

    def __and__(self, other):
        if isinstance(other, _TensorGreater):
            if self.rhs == other.rhs: 
                left = self.lhs
                left_open = isinstance(self, TensorLess)
                
                right = other.lhs
                right_open = isinstance(other, TensorGreater)
                
                if left_open:
                    if right_open:
                        ...
                    else:
                        if left >= right:
                            return S.false
                        return TensorRelational.__and__(self, other)
        elif isinstance(other, _TensorLess):
            if self.lhs == other.lhs: 
                from sympy import Min
                if self.func == other.func:
                    m = Min(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other

        return TensorInequality.__and__(self, other)

    def limit(self, x, xlim, direction=True):
        """ Compute limit x->xlim.
        """
        return TensorLessEqual(self.lhs.limit(x, xlim, direction), self.rhs.limit(x, xlim, direction), given=self, evaluate=False)


class TensorGreaterEqual(_TensorGreater):
    """Class representations of inequalities.

    Explanation
    ===========

    The ``*Than`` classes represent inequal relationships, where the left-hand
    side is generally bigger or smaller than the right-hand side.  For example,
    the TensorGreaterEqual class represents an inequal relationship where the
    left-hand side is at least as big as the right side, if not bigger.  In
    mathematical notation:

    lhs >= rhs

    In total, there are four ``*Than`` classes, to represent the four
    inequalities:

    +-----------------+--------+
    |Class Name       | Symbol |
    +=================+========+
    |TensorGreaterEqual      | (>=)   |
    +-----------------+--------+
    |TensorLessEqual         | (<=)   |
    +-----------------+--------+
    |TensorGreater| (>)    |
    +-----------------+--------+
    |TensorLess   | (<)    |
    +-----------------+--------+

    All classes take two arguments, lhs and rhs.

    +----------------------------+-----------------+
    |Signature Example           | Math equivalent |
    +============================+=================+
    |TensorGreaterEqual(lhs, rhs)       |   lhs >= rhs    |
    +----------------------------+-----------------+
    |TensorLessEqual(lhs, rhs)          |   lhs <= rhs    |
    +----------------------------+-----------------+
    |TensorGreater(lhs, rhs) |   lhs >  rhs    |
    +----------------------------+-----------------+
    |TensorLess(lhs, rhs)    |   lhs <  rhs    |
    +----------------------------+-----------------+

    In addition to the normal .lhs and .rhs of Relations, ``*Than`` inequality
    objects also have the .lts and .gts properties, which represent the "less
    than side" and "greater than side" of the operator.  Use of .lts and .gts
    in an algorithm rather than .lhs and .rhs as an assumption of inequality
    direction will make more explicit the intent of a certain section of code,
    and will make it similarly more robust to client code changes:

    >>> from sympy import TensorGreaterEqual, TensorGreater
    >>> from sympy import TensorLessEqual,    TensorLess
    >>> from sympy import And, Ge, Gt, Le, Lt, Rel, S
    >>> from sympy.abc import x, y, z
    >>> from sympy.core.relational import TensorRelational

    >>> e = TensorGreaterEqual(x, 1)
    >>> e
    x >= 1
    >>> '%s >= %s is the same as %s <= %s' % (e.gts, e.lts, e.lts, e.gts)
    'x >= 1 is the same as 1 <= x'

    Examples
    ========

    One generally does not instantiate these classes directly, but uses various
    convenience methods:

    >>> for f in [Ge, Gt, Le, Lt]:  # convenience wrappers
    ...     print(f(x, 2))
    x >= 2
    x > 2
    x <= 2
    x < 2

    Another option is to use the Python inequality operators (>=, >, <=, <)
    directly.  Their main advantage over the Ge, Gt, Le, and Lt counterparts,
    is that one can write a more "mathematical looking" statement rather than
    littering the math with oddball function calls.  However there are certain
    (minor) caveats of which to be aware (search for 'gotcha', below).

    >>> x >= 2
    x >= 2
    >>> _ == Ge(x, 2)
    True

    However, it is also perfectly valid to instantiate a ``*Than`` class less
    succinctly and less conveniently:

    >>> Rel(x, 1, ">")
    x > 1
    >>> TensorRelational(x, 1, ">")
    x > 1

    >>> TensorGreater(x, 1)
    x > 1
    >>> TensorGreaterEqual(x, 1)
    x >= 1
    >>> TensorLessEqual(x, 1)
    x <= 1
    >>> TensorLess(x, 1)
    x < 1

    Notes
    =====

    There are a couple of "gotchas" to be aware of when using Python's
    operators.

    The first is that what your write is not always what you get:

        >>> 1 < x
        x > 1

        Due to the order that Python parses a statement, it may
        not immediately find two objects comparable.  When "1 < x"
        is evaluated, Python recognizes that the number 1 is a native
        number and that x is *not*.  Because a native Python number does
        not know how to compare itself with a SymPy object
        Python will try the reflective operation, "x > 1" and that is the
        form that gets evaluated, hence returned.

        If the order of the statement is important (for visual output to
        the console, perhaps), one can work around this annoyance in a
        couple ways:

        (1) "sympify" the literal before comparison

        >>> S(1) < x
        1 < x

        (2) use one of the wrappers or less succinct methods described
        above

        >>> Lt(1, x)
        1 < x
        >>> TensorRelational(1, x, "<")
        1 < x

    The second gotcha involves writing equality tests between relationals
    when one or both sides of the test involve a literal relational:

        >>> e = x < 1; e
        x < 1
        >>> e == e  # neither side is a literal
        True
        >>> e == x < 1  # expecting True, too
        False
        >>> e != x < 1  # expecting False
        x < 1
        >>> x < 1 != x < 1  # expecting False or the same thing as before
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of TensorRelational

        The solution for this case is to wrap literal relationals in
        parentheses:

        >>> e == (x < 1)
        True
        >>> e != (x < 1)
        False
        >>> (x < 1) != (x < 1)
        False

    The third gotcha involves chained inequalities not involving
    '==' or '!='. Occasionally, one may be tempted to write:

        >>> e = x < y < z
        Traceback (most recent call last):
        ...
        TypeError: symbolic boolean expression has no truth value.

        Due to an implementation detail or decision of Python [1]_,
        there is no way for SymPy to create a chained inequality with
        that syntax so one must use And:

        >>> e = And(x < y, y < z)
        >>> type( e )
        And
        >>> e
        (x < y) & (y < z)

        Although this can also be done with the '&' operator, it cannot
        be done with the 'and' operarator:

        >>> (x < y) & (y < z)
        (x < y) & (y < z)
        >>> (x < y) and (y < z)
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of TensorRelational

    .. [1] This implementation detail is that Python provides no reliable
       method to determine that a chained inequality is being built.
       Chained comparison operators are evaluated pairwise, using "and"
       logic (see
       http://docs.python.org/2/reference/expressions.html#notin). This
       is done in an efficient way, so that each object being compared
       is only evaluated once and the comparison can short-circuit. For
       example, ``1 > 2 > 3`` is evaluated by Python as ``(1 > 2) and (2
       > 3)``. The ``and`` operator coerces each side into a bool,
       returning the object itself when it short-circuits. The bool of
       the --Than operators will raise TypeError on purpose, because
       SymPy cannot determine the mathematical ordering of symbolic
       expressions. Thus, if we were to compute ``x > y > z``, with
       ``x``, ``y``, and ``z`` being Symbols, Python converts the
       statement (roughly) into these steps:

        (1) x > y > z
        (2) (x > y) and (y > z)
        (3) (GreaterThanObject) and (y > z)
        (4) (GreaterThanObject.__bool__()) and (y > z)
        (5) TypeError

       Because of the "and" added at step 2, the statement gets turned into a
       weak ternary statement, and the first object's __bool__ method will
       raise TypeError.  Thus, creating a chained inequality is not possible.

           In Python, there is no way to override the ``and`` operator, or to
           control how it short circuits, so it is impossible to make something
           like ``x > y > z`` work.  There was a PEP to change this,
           :pep:`335`, but it was officially closed in March, 2012.

    """
    __slots__ = ()

    rel_op = '>='
    scalar_operator = GreaterEqual
    
    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__ge__(rhs))

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
            from sympy.sets import Element, Interval
            return Element(1 / self.lhs, Interval(0, 1 / self.rhs, left_open=True))
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)

        return self

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, TensorEqual):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        return TensorBinaryCondition.subs(self, *args, **kwargs) 

    def __and__(self, other):
        if isinstance(other, TensorGreaterEqual):
            if self.lhs == other.rhs:
                if other.lhs == self.rhs:
                    return TensorEqual(*self.args)
                if other.lhs < self.rhs:
                    return S.false
            elif self.lhs == other.lhs:
                # x >= a, x >= b
                if self.rhs >= other.rhs:
                    return self
                if self.rhs <= other.rhs:
                    return other
                
        elif isinstance(other, TensorLessEqual):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return TensorEqual(*self.args)
                if other.rhs < self.rhs:
                    return S.false
        if isinstance(other, TensorLess):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.false
        elif isinstance(other, TensorGreater):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return other
#                 x >= 1 and x > 0
                if self.rhs > other.rhs:
                    return self
        elif isinstance(other, TensorUnequal):
            if {*self.args} == {*other.args}:
                return TensorGreater(self.lhs, self.rhs)            
        elif isinstance(other, TensorEqual):
            if {*self.args} == {*other.args}:
                return other
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.right_open:
                        if self.rhs >= other.rhs.stop:
                            return S.false
                    else:
                        if self.rhs > other.rhs.stop:
                            return S.false
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.left_open and self.rhs > other.rhs.start or \
                    not other.rhs.left_open and self.rhs >= other.rhs.start:
                        if other.rhs.right_open:
                            if self.lhs < other.rhs.stop:
                                return S.false
                        else:
                            if self.lhs <= other.rhs.stop:
                                return S.false
                
        return _TensorGreater.__and__(self, other)

    def __mul__(self, other):
        if isinstance(other, TensorGreaterEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given={self, other})
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorGreater):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorLess):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return TensorLessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return TensorGreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
                
        return TensorRelational.__mul__(self, other)

    def __or__(self, other):
        if other.is_Equal:
            if {*other.args} == {*self.args}:
                return self
            
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs == other.rhs + 1:
#                 x >= 3 and x == 2 => x >= 2
                return self.func(*other.args)
        elif other.is_Unequal:
            if other.lhs == self.lhs and other.rhs >= self.rhs or \
            other.lhs == self.rhs and self.rhs >= other.rhs or \
            other.rhs == self.lhs and other.lhs >= self.rhs or \
            other.rhs == self.rhs and self.lhs >= other.rhs:
                return S.true
        elif other.is_Less:
#             x >= -1 | x < 0
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
                
        elif other.is_LessEqual:
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
                # x >= 1 and x <= 0
                if self.lhs.is_integer and self.rhs <= other.rhs + 1:
                    return S.true
            
        elif other.is_GreaterEqual:
            if self.lhs == other.lhs:
                # x >= a or x >= a + 1
                if self.rhs >= other.rhs:
                    return other
                if self.rhs <= other.rhs:
                    return self
            
        return TensorRelational.__or__(self, other)

    def simplify(self, deep=False, wrt=None):
        if self.lhs.is_Maxima:
            maximize = self.lhs
            if maximize.expr == self.rhs:
                if all(len(limit) == 1 for limit in maximize.limits):
                    return S.true
        return TensorRelational.simplify(self, deep=deep, wrt=wrt)
    
    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_GreaterEqual:
                a, b = cls.args
                cls = Basic.__new__(TensorLessEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_LessEqual:
                a, b = cls.args
                cls = Basic.__new__(TensorGreaterEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res


ge = TensorGreaterEqual


class TensorLessEqual(_TensorLess):
    __doc__ = TensorGreaterEqual.__doc__
    __slots__ = ()

    rel_op = '<='
    scalar_operator = LessEqual
    
    def __add__(self, other):
        other = sympify(other)
        if isinstance(other, (TensorLess, TensorLessEqual)):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return TensorRelational.__add__(self, other)

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
            from sympy.sets import Element, Interval
            return Element(1 / self.lhs, Interval(1 / self.rhs, 0, right_open=True))

        return self

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__le__(rhs))

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, TensorEqual):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                res = self
                for k, v in eq.items():
                    res = res._subs(k, v)
                return res
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self

        if all(isinstance(arg, TensorRelational) for arg in args):
            free_symbols = self.free_symbols
            f = self.lhs - self.rhs
            given = []
            for eq in args:
                if eq.plausible:
                    given.append(eq)
                old, new = eq.args
                if old in free_symbols:
                    domain = old.domain & old.domain_conditioned(eq)
                    if domain != old.domain:
                        _old = Symbol(old.name, domain=domain)
                        f = f.subs(old, _old)
                else:
                    return self

            maxi = f.max()
            if self.plausible:
                return TensorLessEqual(maxi, 0, imply=self, given=given)
            return self

        old, new = args
       
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return TensorLess(lhs, rhs, given=self)
            if _g <= g:
                return TensorLessEqual(lhs, rhs, given=self)

            if _g > g:
                return TensorGreaterEqual(lhs, rhs, given=self)
            if _g >= g:
                return TensorGreater(lhs, rhs, given=self)
        return TensorBinaryCondition.subs(self, *args, **kwargs)

    def __and__(self, other):
        if other.is_LessEqual:
            if self.lhs == other.rhs:
                if other.lhs == self.rhs:
                    return TensorEqual(self.lhs, self.rhs)
                if other.lhs > self.rhs:
                    return S.false
            elif self.lhs == other.lhs:
                # x <= a, x <= b
                if self.rhs <= other.rhs:
                    return self
                
                if self.rhs >= other.rhs:
                    return other
                
        elif other.is_Less:
            if self.lhs == other.lhs:
#                 x <= 1 and x < 0
                if self.rhs >= other.rhs:
                    return other
#                 x <= 0 and x < 1
                if self.rhs < other.rhs:
                    return self

            elif self.lhs == other.rhs:
                if other.lhs >= self.rhs:
                    return S.false
        elif other.is_GreaterEqual:
            if self.lhs == other.lhs:
                if other.rhs == self.rhs:
                    return TensorEqual(self.lhs, self.rhs)
                if other.rhs > self.rhs:
                    return S.false
        elif other.is_Greater:
            if self.lhs == other.lhs:
                if other.rhs >= self.rhs:
                    return S.false
            elif self.rhs == other.rhs:
                if other.lhs <= self.lhs:
                    return S.false
                
        elif other.is_Element:
            if other.rhs.is_Range:
                if self.lhs == other.lhs:
                    if self.rhs < other.rhs.start:
                        return S.false

                    return other.func(self.lhs, other.rhs.func(S.NegativeInfinity, self.rhs + 1) & other.rhs).simplify()
            elif other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.left_open:
                        if self.rhs <= other.rhs.start:
                            return S.false
                    else:
                        if self.rhs < other.rhs.start:
                            return S.false

                    return other.func(self.lhs, other.rhs.func(S.NegativeInfinity, self.rhs) & other.rhs).simplify()
                
        elif other.is_Unequal:
            if {*self.args} == {*other.args}:
                return TensorLess(*self.args)
            
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.right_open and self.rhs < other.rhs.stop or \
                    not other.rhs.right_open and self.rhs <= other.rhs.stop:
                        if other.rhs.left_open:
                            if self.lhs > other.rhs.start:
                                return S.false
                        else:
                            if self.lhs >= other.rhs.start:
                                return S.false
            
        return _TensorLess.__and__(self, other)

    def __mul__(self, other):
        if isinstance(other, TensorLessEqual):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorGreater):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        
        return TensorRelational.__mul__(self, other)

    def __or__(self, other):
        if other.is_Equal:
            if {*other.args} == {*self.args}:
                return self
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs + 1 == other.rhs:
#                 x <= 3 and x == 4 => x >= 4
                return self.func(*other.args)
            
        elif other.is_Unequal:
            if other.lhs == self.lhs and other.rhs <= self.rhs or \
            other.lhs == self.rhs and self.rhs <= other.rhs or \
            other.rhs == self.lhs and other.lhs <= self.rhs or \
            other.rhs == self.rhs and self.lhs <= other.rhs:
                return S.true
            
        elif other.is_Greater:
#             x <= 1 | x > 0
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true
        elif other.is_GreaterEqual:
#             x <= 1 | x > 0
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true
                # x <= 0 and x >= 1
                if self.lhs.is_integer:
                    if self.rhs + 1 >= other.rhs:
                        return S.true
        elif other.is_LessEqual:
            if self.lhs == other.lhs:
                # x < a or x < a + 1
                if self.rhs <= other.rhs:
                    return other
                if self.rhs >= other.rhs:
                    return self
            
        return TensorRelational.__or__(self, other)

    def simplify(self, deep=False, wrt=None):
        if self.lhs.is_Minima:
            minimize = self.lhs
            if minimize.expr == self.rhs:
                if all(len(limit) == 1 for limit in minimize.limits):
                    return S.true
        return TensorRelational.simplify(self, deep=deep, wrt=wrt)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_LessEqual:
                a, b = cls.args
                cls = Basic.__new__(TensorGreaterEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_GreaterEqual:
                a, b = cls.args
                cls = Basic.__new__(TensorLessEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res


le = TensorLessEqual


class TensorGreater(_TensorGreater):
    __doc__ = TensorGreaterEqual.__doc__
    __slots__ = ()

    rel_op = '>'
    invert_type = TensorLessEqual
    scalar_operator = Greater
    
    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__gt__(rhs))

    def __add__(self, other):
        other = sympify(other)
        if other.is_Equal: 
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif other.is__Greater:
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return self.func(self.lhs + other, self.rhs + other)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, TensorEqual):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        
        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return TensorBinaryCondition.subs(self, *args, **kwargs)
            
    def is_positive_relationship(self):
        if self.rhs.is_zero:
            return self.lhs

    def __and__(self, other):
        if isinstance(other, TensorLess):
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs: 
                    return S.false
#                 x > a and x < b
                if self.lhs.is_integer:
                    # x in (b; a)
                    from sympy import Range
                    if not Range(self.rhs, other.rhs, left_open=True, right_open=True):
                        return S.false
                
        elif isinstance(other, TensorLessEqual):
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs: 
                    return S.false
            elif self.rhs == other.rhs:
                if other.lhs >= self.lhs: 
                    return S.false
                    
        elif isinstance(other, TensorUnequal):
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, TensorEqual):
            if set(self.args) == set(other.args):
                return S.false
            
        elif isinstance(other, _TensorGreater):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return self
#                 x > 0 and x >= 1
                if self.rhs < other.rhs:
                    return other
                
#                 x > a and a >= x + 1
            if self.rhs == other.lhs:
                if self.lhs <= other.rhs:
                    return S.false
                 
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if self.rhs >= other.rhs.stop:
                            return S.false
                
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs: 
                    if self.rhs >= other.rhs.start:
                        if other.rhs.right_open:
                            if self.lhs < other.rhs.stop:
                                return S.false
                        else:
                            if self.lhs <= other.rhs.stop:
                                return S.false
                               
        return _TensorGreater.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, TensorUnequal):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs: 
                    return other
                if self.lhs <= other.rhs:
                    return (self.lhs < other.rhs) | self
            elif self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return other
                if self.lhs <= other.lhs:
                    return (self.lhs < other.lhs) | self
        elif isinstance(other, TensorEqual):
            if set(self.args) == set(other.args):
                return TensorGreaterEqual(self.lhs, self.rhs)
            
        elif isinstance(other, TensorLess):
            if self.lhs == other.lhs:
                if other.rhs > self.rhs:
                    return S.true
                if other.rhs == self.rhs:
                    return TensorUnequal(*self.args)
            if self.rhs == other.rhs:
                if self.lhs > other.lhs:
                    return S.true
        elif isinstance(other, TensorGreater):
            if self.lhs == other.rhs:
                if other.lhs > self.rhs:
                    return S.true
                if other.lhs == self.rhs:
                    return TensorUnequal(*self.args)
                
            if self.rhs == other.lhs:
                if self.lhs > other.rhs:
                    return S.true
                
            if self.lhs == other.lhs:
                # x > a or x > a + 1
                if self.rhs >= other.rhs:
                    return other
                if self.rhs <= other.rhs:
                    return self
                
        elif isinstance(other, TensorLessEqual):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
            if self.rhs == other.rhs:
                if other.lhs <= self.lhs:
                    return S.true
        elif isinstance(other, TensorGreaterEqual):
            if self.lhs == other.rhs:
                if self.rhs <= other.lhs:
                    return S.true
            if self.rhs == other.lhs:
                if other.rhs <= self.lhs:
                    return S.true
            
        return _TensorGreater.__or__(self, other)

    def __mul__(self, other):
        if isinstance(other, TensorGreater):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorGreaterEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return TensorGreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return TensorLessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorLessEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return TensorLessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return TensorGreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorLess):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return TensorLess(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return TensorGreater(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        return TensorRelational.__mul__(self, other)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Greater:
                a, b = cls.args
                cls = Basic.__new__(TensorLess, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_Less:
                a, b = cls.args
                cls = Basic.__new__(TensorGreater, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res


gt = TensorGreater
TensorLessEqual.invert_type = TensorGreater


class TensorLess(_TensorLess):
    __doc__ = TensorGreaterEqual.__doc__
    __slots__ = ()

    rel_op = '<'
    invert_type = TensorGreaterEqual
    scalar_operator = Less
    
    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__lt__(rhs))

    def __add__(self, other):
        other = sympify(other)
        if isinstance(other, TensorEqual):
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif other.is__Less:
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return self.func(self.lhs + other, self.rhs + other)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, TensorEqual):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        return TensorBinaryCondition.subs(self, *args, **kwargs)

    def is_positive_relationship(self):
        if self.lhs.is_zero:
            return self.rhs

    def __and__(self, other):
        if isinstance(other, TensorLess):
            if self.rhs == other.lhs:
                if self.lhs <= other.rhs: 
                    return S.false
                
        elif isinstance(other, TensorGreaterEqual):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.false
                if self.lhs.is_integer and self.rhs == other.rhs + 1:
                    return TensorEqual(*other.args)                
        elif isinstance(other, TensorGreater):
            # x < a and x > b
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs: 
                    return S.false
                if self.lhs.is_integer:
                    # x in (b; a)
                    from sympy import Range
                    if not Range(other.rhs, self.rhs, left_open=True, right_open=True):
                        return S.false
                
        elif isinstance(other, TensorUnequal):
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, TensorEqual):
            if set(self.args) == set(other.args):
                return S.false
        elif isinstance(other, _TensorLess):
            if self.lhs == other.lhs:
#                 x < 0 and x <= 1
                if self.rhs <= other.rhs:
                    return self
#                 x < 1 and x <= 0
                if self.rhs > other.rhs:
                    return other
            if self.rhs == other.lhs:
#                 x < a and a < x - 1
                if self.lhs >= other.rhs:
                    return S.false
        
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if self.rhs <= other.rhs.start:
                        return S.false
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs: 
                    if self.rhs <= other.rhs.stop:
                        if other.rhs.left_open:
                            if self.lhs > other.rhs.start:
                                return S.false
                        else:
                            if self.lhs >= other.rhs.start:
                                return S.false

        return _TensorLess.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, TensorUnequal):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs: 
                    return other
                if self.lhs >= other.rhs:
                    return (self.lhs > other.rhs) | self
            elif self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return other
                if self.lhs >= other.lhs:
                    return (self.lhs > other.lhs) | self
        elif isinstance(other, TensorEqual):
            if set(self.args) == set(other.args):
                return TensorLessEqual(self.lhs, self.rhs)
            
        elif isinstance(other, TensorGreater):
            if self.lhs == other.lhs:
                if self.rhs > other.rhs:
                    return S.true
                if other.rhs == self.rhs:
                    return TensorUnequal(*self.args)
            if self.rhs == other.rhs:
                if other.lhs > self.lhs:
                    return S.true
        elif isinstance(other, TensorLess):
            if self.lhs == other.rhs:
                if self.rhs > other.lhs:
                    return S.true
                if other.lhs == self.rhs:
                    return TensorUnequal(*self.args)
                
            if self.rhs == other.lhs:
                if other.rhs > self.lhs:
                    return S.true
            
            if self.lhs == other.lhs:
                # x < a or x < a + 1
                if self.rhs <= other.rhs:
                    return other
                if self.rhs >= other.rhs:
                    return self
            
        elif isinstance(other, TensorGreaterEqual):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true
            if self.rhs == other.rhs:
                if other.lhs >= self.lhs:
                    return S.true
        elif isinstance(other, TensorLessEqual):
            if self.lhs == other.rhs:
                if self.rhs >= other.lhs:
                    return S.true
            if self.rhs == other.lhs:
                if other.rhs >= self.lhs:
                    return S.true
                                              
        return _TensorLess.__or__(self, other)

    def __mul__(self, other):
        other = sympify(other)
        if isinstance(other, TensorLess):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, TensorGreaterEqual):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonpositive:
                    return TensorGreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return TensorLessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])          
        elif isinstance(other, TensorGreater):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonpositive:
                    return TensorGreater(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return TensorLess(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])          
        elif not other.is_Boolean:
            if other.is_extended_positive:
                return self.func(self.lhs * other, self.rhs * other)
            if other.is_extended_negative:
                return self.reversed_type(self.lhs * other, self.rhs * other)
            elif other.is_extended_nonnegative:
                return TensorLessEqual(self.lhs * other, self.rhs * other, given=self)
            elif other.is_extended_nonpositive:
                return TensorGreaterEqual(self.lhs * other, self.rhs * other, given=self)
            return self

        return TensorRelational.__mul__(self, other)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Less:
                a, b = cls.args
                cls = Basic.__new__(TensorGreater, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_Greater:
                a, b = cls.args
                cls = Basic.__new__(TensorLess, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res


lt = TensorLess
TensorGreaterEqual.invert_type = TensorLess

ge.reversed_type = le
lt.reversed_type = gt
le.reversed_type = ge
ne.reversed_type = ne
eq.reversed_type = eq
gt.reversed_type = lt
