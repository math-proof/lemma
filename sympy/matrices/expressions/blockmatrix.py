from sympy.core import Basic

from sympy.strategies import typed, exhaust, condition, do_one, unpack
from sympy.strategies.traverse import bottom_up
from sympy.utilities import sift

from sympy.matrices.expressions.matexpr import MatrixExpr, Zeros, Identity
from sympy.matrices.expressions.matpow import MatPow
from sympy.matrices.expressions.transpose import Transpose, transpose

from sympy.matrices.expressions.inverse import Inverse
from sympy.matrices import Matrix, ShapeError
from sympy.core.cache import cacheit
from sympy.core.containers import Tuple


class BlockMatrix(MatrixExpr): 
    """
    Represents a block matrix.
    Examples
    ========

    >>> n = Symbol(integer=True, positive=True)
    >>> A = Symbol(shape=(n, n), real=True)
    >>> B = Symbol(shape=(n, n), real=True)
    >>> C = Symbol(shape=(n, n), real=True)
    >>> D = Symbol(shape=(n, n), real=True)
    >>> block1 = BlockMatrix([[A, B], [C, D]])
    >>> block1
    [[A, B], [C, D]]
    >>> _A = Symbol("A'", shape=(n, n), real=True)
    >>> _B = Symbol("B'", shape=(n, n), real=True)
    >>> _C = Symbol("C'", shape=(n, n), real=True)
    >>> _D = Symbol("D'", shape=(n, n), real=True)
    >>> block2 = BlockMatrix([[_A, _C], [_B, _D]])
    >>> block2
    [[A, B], [C, D]]
    >>> discrete.matmul.to.blockMatrix.apply(block1 @ block2, deep=True)
    
    
    """

    def _eval_template_is_attr(self, is_attr):
        b = None
        for expr in self.args:
            a = getattr(expr, is_attr)
            if a is None:
                return
            if b is None:
                b = a
            elif b != a:
                return
        return b

    _eval_is_extended_integer = lambda self: self._eval_template_is_attr('is_extended_integer')
    _eval_is_extended_rational = lambda self: self._eval_template_is_attr('is_extended_rational')
    _eval_is_extended_real = lambda self: self._eval_template_is_attr('is_extended_real')
    _eval_is_extended_complex = lambda self: self._eval_template_is_attr('is_extended_complex')
    _eval_is_finite = lambda self: self._eval_template_is_attr('is_finite')
    _eval_is_extended_positive = lambda self: self._eval_template_is_attr('is_extended_positive')
    _eval_is_extended_negative = lambda self: self._eval_template_is_attr('is_extended_negative')

    def _eval_is_random(self):
        return any(arg.is_random for arg in self.args)

    @property
    def dtype(self):
        dtype = None
        for arg in self.args:
            _dtype = arg.dtype
            if dtype is None or dtype in _dtype:
                dtype = _dtype
        return dtype

    @classmethod
    def is_consistent(cls, mat, blocks):
        if mat.is_BlockMatrix and len(mat.args) == len(blocks):
            for arg, b in zip(mat.args, blocks):
                arg_shape = arg.shape
                if len(arg_shape) < 2:
                    return False
                
                b_shape = b[0].shape
                if len(b_shape) < 2:
                    return False
                
                if arg_shape[-2] != b_shape[-2]:
                    return False
            
            return True
            
    def __new__(cls, *args, **kwargs):
        if len(args) > 1 and isinstance(args[-1], tuple):
            *args, [axis] = args
        elif 'axis' in kwargs:
            axis = kwargs.pop('axis')
        else:
            axis = 0
        _args = []
        from sympy import sympify
        if len(args) == 1 and isinstance(args[0], (list, tuple)):
            args = args[0]
            if all(isinstance(arg, (list, tuple)) for arg in args):
                args = [cls(*(Transpose(x) for x in arr)).T for arr in args]
                
            args = [*map(sympify, args)]
            if all(arg.is_DenseMatrix for arg in args):
                if axis == 0:
                    if len(args[0].shape) == 1:
                        return Matrix(tuple(arr.totuple() for arr in args))
                    
                    if len(args[0].shape) == 2:
                        ret = []
                        for arr in args:
                            arr = arr.totuple()
                            ret.extend(arr)
                        return Matrix(tuple(ret))

                if axis == 1:
                    rows = args[0].shape[0]
                    ret = [() for i in range(rows)]
                    for arr in args:
                        arr = arr.totuple()
                        for i in range(rows):
                            ret[i] += arr[i]

                    return Matrix(tuple(ret))
        else:        
            args = [*map(sympify, args)]

        length = max(len(arg.shape) for arg in args)
#         shape = kwargs.get('shape')
        if axis == 1:
            hit = False
            for i, arg in enumerate(args):
                if len(arg.shape) == length:
                    if isinstance(arg, BlockMatrix):
                        if arg.axis == 0:
                            blocks = arg.blocks
                            if blocks is None:
                                blocks = [(arg,) for arg in arg.args]

                            for j in range(i + 1, len(args)):
                                arg = args[j]
                                if isinstance(arg, BlockMatrix) and arg.axis == 0:
                                    continue
                                else:
                                    break
                            else:
                                hit = True
                    break
                        
            if hit:
                former = args[:i]
                latter = args[i + 1:]
                
                hit = False
                together = former + latter
                assert together
                if all(cls.is_consistent(mat, blocks) for mat in together):
                    former = [mat.args for mat in former]
                    latter = [mat.args for mat in latter]
                    
                    matrix = []
                    for args in zip(*former, blocks, *latter):
                        
                        arr = []
                        for b in args:
                            if isinstance(b, (tuple, list)):
                                arr.extend(b)
                            else:
                                arr.append(b)
                        
                        matrix.append(arr)
                    return BlockMatrix(matrix)
                
        is_DenseMatrix = True
        for arg in args: 
            if isinstance(arg, BlockMatrix) and len(arg.shape) == length and arg.axis == axis:
                _args += arg.args
            else:
                _args.append(arg)
                if not arg.is_DenseMatrix:
                    is_DenseMatrix = False
                    
        if length == 1:
            if is_DenseMatrix:
                if all(not arg.shape for arg in _args):
                    return Matrix(tuple(_args))
            else:
                if len(_args) == 1:
                    return _args[0]
                axis = 0
        elif not length:
            return Matrix(tuple(_args))
        
        blocks = Basic.__new__(cls, *_args, **kwargs)
        blocks.axis = sympify(axis)
        return blocks
    
    @property
    def kwargs(self):
        # return hyper parameter of this object
        return {'axis': self.axis}
           
    @cacheit
    def _eval_shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
         
        if self.axis:
            from std import argmax
            shapes = [arg.shape for arg in self.args]
            len_shapes = [len(shape) for shape in shapes]
            max_length_index = argmax(len_shapes)
            max_length = len_shapes[max_length_index]
            assert self.axis < max_length
            
            for axis in {*range(max_length)} - {self.axis}:
                if len({s[axis] for s in shapes}) > 1:
                    print([s[axis] for s in shapes])
                assert len({s[axis] for s in shapes}) == 1

            shape = shapes[max_length_index]
            dimension_axis = 0
            for s in shapes:
                if self.axis < len(s):
                    dimension_axis += s[self.axis]
                else:
                    dimension_axis += 1
            return shape[:self.axis] + (dimension_axis,) + shape[self.axis + 1:max_length]
        else:
            shapes = [arg.shape for arg in self.args]
            if max(len(s) for s in shapes) == 1:
                cols = 0
                for s in shapes:
                    if s:
                        cols += s[0]
                    else:
                        cols += 1
                return (cols,)
            else:
                from sympy.core.add import Add
                Add.broadcast(shapes)
                rows = sum(s[0] for s in shapes)
                if len(shapes[0]) > 1:
                    return (rows, *shapes[0][1:])
                else:
                    return (rows,)
                
    def get_slice(self, indices):
        axis = int(self.axis)
        #indices is indexing at position axis
        start, stop, step = indices.slice_args
        if start == 0 and stop == self.shape[axis]:
            return self
        
        from sympy import Piecewise
        assert step == 1
        
        index_stop = 0
        args = []
        len_shape = len(self.shape)
        index_start = [0] * len(self.args)
        
        for i, arg in enumerate(self.args):
            if i:
                index_start[i] = index_start[i - 1] + size
                
            if len(arg.shape) < len_shape:
                size = 1
            else:
                size = arg.shape[axis]
                
            index_stop += size
                
            cond = stop <= index_stop
            if cond == False:
                continue
            
            args_inner = []
            for j in range(i, -1, -1):
                cond_inner = index_start[j] <= start
                if cond_inner == False:
                    continue
                
                blocks = []
                for k in range(j, i + 1):
                    arg = self.args[k]
                    if len(arg.shape) < len_shape:
                        blocks.append(arg)
                    else:
                        if k == j:
                            if k == i:
                                slices = [slice(None)] * axis + [slice(start - index_start[k], stop - index_start[k])]
                                blocks.append(arg[slices])
                            else:
                                slices = [slice(None)] * axis + [slice(start - index_start[k], None)]
                                blocks.append(arg[slices])
                        else:
                            if k == i:
                                slices = [slice(None)] * axis + [slice(None, stop - index_start[k])]
                                blocks.append(arg[slices])
                            else:
                                blocks.append(arg)
                            
                if len(blocks) == 1:
                    blocks, = blocks
                else:
                    blocks = self.func(blocks, axis=axis)

                args_inner.append([blocks, cond_inner])
                if cond_inner:
                    break
                
            args_inner[-1][1] = True
            args.append([Piecewise(*args_inner), cond])

            if cond:
                break

        args[-1][1] = True
        return Piecewise(*args)
        
    def get_piece(self, indices):
        axis = int(self.axis)
        #indices is indexing at position axis
        from sympy import Piecewise 
        rows = 0
        args = []
        len_shape = len(self.shape)
        for arg in self.args:
            index = rows
            if len(arg.shape) < len_shape:
                rows += 1
            else:
                rows += arg.shape[axis]
                
            cond = indices < rows
            if cond == False:
                continue
            
            if len(arg.shape) < len_shape:
                args.append([arg, cond])
            else:
                args.append([arg[indices - index], cond])
                
            if cond:
                break

        args[-1][-1] = True
        return Piecewise(*args)
        
    def __getitem__(self, indices):
        if (indices := self.simplify_indices(indices)) is None:
            return self

        if isinstance(indices, Tuple):
            axis = self.axis
            if axis != 0:
                args = [arg[indices] for arg in self.args]
                return self.func(*args, axis=axis)
            
            return self.get_slice(indices)

        if isinstance(indices, tuple):
            if len(indices) >= 2:
                if indices[self.axis] == Tuple(0, self.shape[self.axis]):
                    indices = indices[:self.axis] + (slice(None),) + indices[self.axis + 1:]
                    if self.axis == 0:
                        args = []
                        for v in self.args:
                            if len(v.shape) < len(self.shape):
                                indexed = v[indices[1:]]
                            else:
                                indexed = v[indices]
                            args.append(indexed)
                    else:
                        args = [arg[indices] for arg in self.args]
                    return self.func(*args, axis=self.axis)

                indices, j = indices
                if isinstance(j, Tuple):
                    if isinstance(indices, Tuple):
                        if indices != Tuple(0, self.shape[0]):
                            return self[indices][:, j]
                        
                        assert self.axis == 1
                        return self.get_slice(j)
                    return self[indices][j]
        else:
            j = None
                  
        if self.axis == 0:
            if isinstance(indices, Tuple):
                self = self.get_slice(indices)
                if j is not None:
                    self = self[:, j]
            else:
                self = self.get_piece(indices)
                if j is not None:
                    self = self[j]
            return self
        
        if isinstance(indices, Tuple):
            if indices == Tuple(0, self.shape[0]):
                self = self.get_piece(j)
            else:
                self = self.func(*(a[indices] for a in self.args), axis=self.axis - 1)
                if j is not None:
                    self = self[j]
            return self
            
        self = self.func(*(a[indices] for a in self.args), axis=self.axis - 1)
        if j is not None:
            self = self[j]
        return self

    def _eval_determinant(self, **kwargs):
        from sympy.concrete.products import Product
        if self.is_upper or self.is_lower:
            i = self.generate_var(integer=True)
            return Product(self[i, i], (i, 0, self.cols)).doit()

    @property
    def is_lower(self):
        if blocks := self.blocks:
            m = len(blocks)
            n = len(blocks[0])
            if m == n:
                if all(blocks[i][j].is_zero for j in range(1, m) for i in range(j)):
                    if all(blocks[i][i].is_lower for i in range(m)):
                        return True

        from sympy import Range, Min
        i = self.generate_var(domain=Range(Min(self.rows, self.cols - 1)))
        j = i.generate_var(free_symbols=self.free_symbols, domain=Range(i + 1, self.cols))
        assert i < j
        if self[i, j].is_zero:
            return True

    @property
    def is_upper(self):
        if blocks := self.blocks:
            m = len(blocks)
            n = len(blocks[0])
            if m == n:
                if all(blocks[i][j].is_zero for i in range(1, m) for j in range(i)):
                    if all(blocks[i][i].is_upper for i in range(m)):
                        return True

        from sympy import Range, Min
        j = self.generate_var(domain=Range(Min(self.cols, self.rows - 1)))
        i = j.generate_var(free_symbols=self.free_symbols, domain=Range(j + 1, self.rows))
        assert i > j
        if self[i, j].is_zero:
            return True

    def __add__(self, other):
        if isinstance(other, BlockMatrix):
            if self.axis == other.axis:
                if len(self.args) == len(other.args):
                    if all(x.shape == y.shape for x, y in zip(self.args, other.args)):
                        return self.func(*[x + y for x, y in zip(self.args, other.args)], shape=self.shape)
        return MatrixExpr.__add__(self, other)

    def simplify(self, deep=False, **kwargs):
        if deep:
            return MatrixExpr.simplify(self, deep=deep, **kwargs)
        if self.axis == 0:
            if self.shape[0] == len(self.args):
                start = None
                mat = []
                for i, arg in enumerate(self.args):
                    if arg.is_Indexed:
                        diff = arg.indices[-1] - i
                        if start is None:
                            start = diff
                        else:
                            if start != diff:
                                return self
                    elif arg.is_DenseMatrix:
                        mat.append(arg)
                    else:
                        return self
                    
                if start is not None:
                    return arg.base[start:len(self.args)]
                
                if len(mat) == len(self.args):
                    return self.to_DenseMatrix()
                else:
                    return self
            
            b = None
            from sympy import S
            start, stop = None, None
            rest = None
            for arg in self.args:
                if arg.is_Sliced or arg.is_Indexed:
                    if b is None:
                        b = arg.base
                    elif arg.base.is_Indexed and arg.base.base == b:
                        ...
                    elif b != arg.base or len(arg.indices) > 1:
                        b = None
                        break
                                        
                    if start is None:
                        if arg.is_Sliced:
                            (start, stop), *_rest = arg.indices
                        else:
                            start = arg.index
                            stop = start + S.One
                            _rest = []
                    else:
                        if arg.is_Sliced:
                            if arg.base.is_Indexed and arg.base.base == b:
                                _start = arg.base.index
                                _stop = _start + S.One
                                [*_rest] = arg.indices
                            else:
                                (_start, _stop), *_rest = arg.indices
                        else:
                            _start = arg.index
                            _stop = _start + S.One
                            _rest = []
                            
                        if _start == stop:
                            stop = _stop
                        elif _stop == start:
                            start = _start
                        else:
                            b = None
                            break

                    if rest is None:
                        rest = _rest
                    elif rest != _rest:
                        b = None
                        break
                else:
                    b = None
                    break
                    
            if b is not None:
                if rest:
                    rest.insert(0, slice(start, stop))
                    return b[tuple(rest)]
                else:
                    return b[start:stop]
            
            mat = []
            for arg in self.args:
                if arg.is_DenseMatrix:
                    if not mat or mat[0].is_DenseMatrix:
                        mat.append(arg)
                elif arg.is_Zeros:
                    if not mat or mat[0].is_Zeros:
                        mat.append(arg)

            if len(mat) == len(self.args):
                if mat[0].is_DenseMatrix:
                    return self.to_DenseMatrix()
                
                if mat[0].is_Zeros:
                    return Zeros(*self.shape)

        elif self.axis == 1:
            if blocks := self.blocks:
                return self.func(blocks)
            
        return self
    
    def to_DenseMatrix(self):
        args = []
        for m in self.args:
            args.extend(m._args)
        return Matrix(*args, shape=self.shape)
            
    @property
    def blocks(self):
        if len(self.shape) != 2:
            return
        
        cols = None
        blocks = []
        for X in self.args: 
            if not X.is_BlockMatrix:
                return
            
            if len(X.shape) == 2 and self.axis + X.axis == 1:
                if cols is None:
                    cols = len(X.args)
                else:
                    if cols != len(X.args):
                        return
                    
            elif len(X.shape) == 1:
                if cols is None:
                    cols = len(X.args)
                else:
                    if cols != len(X.args):
                        return
            else:
                return
            
            blocks.append(X.args)
        
        if (self.axis - 1, self.axis) == self.default_axis:
            rows = cols
            cols = len(blocks)
            for row in range(rows):
                shape_set = set()
                for col in range(cols):    
                    shape = blocks[col][row].shape
                    if len(shape) >= 2:
                        shape_set.add(shape[-2])
                    else:
                        break
                    
                    if len(shape_set) > 1:
                        return
                    
            blocks = [*zip(*blocks)]
            
        for i in range(cols):
            cols = None
            block = [block[i] for block in blocks]
            matrix = [b for b in block if len(b.shape) == 2]           
            
            if matrix:
                shape = matrix[0].shape
                if len(shape) == 2:
                    cols = shape[-1]
                else:
                    cols = shape[-1]
                    
                if any(m.shape[-1] != cols for m in matrix):
                    return
                
                vector = [b for b in block if len(b.shape) == 1]
                if any(v.shape[0] != cols for v in vector):
                    return
                
        return blocks
        
    # {c} means center, {l} means left, {r} means right
    def _latex(self, p):
#         return r'\begin{pmatrix}%s\end{pmatrix}' % r'\\'.join('{%s}' % self._print(arg) for arg in expr.args)

        blocks = self.blocks
        if blocks is not None:
            cols = len(blocks[0])
            array = (' & '.join('{%s}' % p._print(X) for X in block) for block in blocks)
            latex = r"\left[\begin{array}{%s}%s\end{array}\right]" % ('c' * cols, r'\\'.join(array))
            if self.axis:
                latex = "%s_%s" % (latex, p._print(self.axis))
                
            return latex
            
        array = []
        for X in self.args: 
            if X.is_Transpose and X.arg.is_BlockMatrix: 
                X = X.arg
                latex = r"{\left(\begin{array}{%s}%s\end{array}\right)}" % ('c' * len(X.args), ' & '.join('{%s}' % p._print(arg.T) for arg in X.args))
            else:
                latex = '{%s}' % p._print(X)   
            array.append(latex)

        if len(self.shape) == 1 or self.axis:
            delimiter = ' & '
            center = 'c' * len(self.args)
        else:
            delimiter = r'\\'
            center = 'c'
            
        latex = r"\left[\begin{array}{%s}%s\end{array}\right]" % (center, delimiter.join(array))
        if self.axis:
            latex = "%s_%s" % (latex, p._print(self.axis))
        return latex
#         return r"\begin{equation}\left(\begin{array}{c}%s\end{array}\right)\end{equation}" % r'\\'.join('{%s}' % self._print(arg) for arg in expr.args)

    def _sympystr(self, p):
        blocks = self.blocks
        if blocks is not None:
            blocks = [[p._print(cell) for cell in block] for block in blocks]
            
            rows = len(blocks)
            cols = len(blocks[0])
            col_width = [max(len(blocks[i][j]) for i in range(rows)) for j in range(cols)]
            
            for i in range(rows):
                for j in range(cols):
                    diff = col_width[j] - len(blocks[i][j])
                    if diff:
                        blocks[i][j] = ' ' * diff + blocks[i][j]

            indent = p._context.get('indent', 0) + 1
            newline = '\n' + '    ' * indent
            return "[%s]" % (newline + f',{newline}'.join(['[%s]' % ', '.join(row) for row in blocks]))
            
        array = []
        for X in self.args: 
            array.append(p._print(X))

        tex = ", ".join(array)
        if self.axis:
            tex = "BlockMatrix[%s](%s)" % (p._print(self.axis), tex)
        else:
            tex = "[%s]" % tex
        return tex

    def _lean(self, p):
        blocks = self.blocks
        if blocks is not None:
            blocks = [[p._print(cell) for cell in block] for block in blocks]
            
            rows = len(blocks)
            cols = len(blocks[0])
            col_width = [max(len(blocks[i][j]) for i in range(rows)) for j in range(cols)]
            
            for i in range(rows):
                for j in range(cols):
                    diff = col_width[j] - len(blocks[i][j])
                    if diff:
                        blocks[i][j] = ' ' * diff + blocks[i][j]

            indent = p._context.get('indent', 0) + 1
            newline = '\n' + '    ' * indent
            return "[%s]" % (newline + f',{newline}'.join(['[%s]' % ', '.join(row) for row in blocks]))
            
        array = []
        for X in self.args: 
            array.append(p._print(X))

        tex = ", ".join(array)
        if self.axis:
            tex = "BlockMatrix[%s](%s)" % (p._print(self.axis), tex)
        else:
            tex = "[%s]" % tex
        return tex
    
    def _pretty(self, p): 
        return p._print_seq(self.args, '[', ']')
    
    @cacheit
    def _eval_domain_defined(self, x, **_):
        if x.dtype.is_set:
            return x.universalSet
        
        domain = x.domain
        for arg in self.args:
            domain &= arg.domain_defined(x, allow_empty=True)
        return domain

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            len_shape = len(self.shape)
            
            if len_shape == 1:
                return self
                    
            args = [mat.T for mat in self.args]
            if self.axis == len_shape - 1:
                return self.func(*args, axis=len_shape - 2)
    
            if self.axis == len_shape - 2:
                return self.func(*args, axis=len_shape - 1)
            
            return self.func(*args)
    

    def __rmul__(self, other): 
        if not other.shape:
            return self.func(*(other * arg for arg in self.args), **self.kwargs)
        return MatrixExpr.__rmul__(self, other)

    def _subs(self, old, new, **hints):
        if old.is_BlockMatrix and self.axis == old.axis:
            from std.search import sunday
            i = sunday(self.args, old.args)
            if i >= 0:
                args = self.args[:i]
                
                rest = self.args[i + len(old.args):]
                if not i and not rest:
                    return new
                
                if new.is_BlockMatrix and new.axis == self.axis:
                    args += new.args
                else:
                    args += (new,)
                    
                args += rest
                return self.func(*args, **self.kwargs).simplify()
                
        if old == new:
            return self

        if old.is_Sliced:
            this = self._subs_sliced(old, new, **hints)
            if this != self:
                return this

        args = [*self.args]
        indicesToDelete = []
        for i, arg in enumerate(args):
            try:
                arg = arg._subs(old, new, **hints)
                if arg != self.args[i]:
                    if any(s.is_zero for s in arg.shape):
                        raise Exception('empty slices')
                    args[i] = arg

            except Exception as e:
                if str(e) == 'empty slices':
                    if any(s._has(old) for s in args[i].shape):
                        indicesToDelete.append(i)
                        continue
                
                raise e
        
        if indicesToDelete:
            for i in reversed(indicesToDelete):
                del args[i]
                
            if not args:
                raise Exception('empty slices')
        
        return self.func(*args, **self.kwargs)


    def of(self, cls):
        if cls.is_IndexedOperator:
            if cls.func.is_BlockMatrix:
                if len(cls.limits) == 1:
                    [limit] = cls.limits
                    if len(limit) == 1:
                        [axis] = limit
                        if axis == self.axis:
                            return self.args
                        
                if self.axis == 0:
                    return MatrixExpr.of(self, cls)
                    
        elif isinstance(cls, type):
            if cls.is_BlockMatrix:
                if not self.axis:
                    return self.args
            
            elif isinstance(self, cls):
                return self
            
        elif cls.is_BlockMatrix:#of Basic type
            axis = cls.kwargs.get('axis', 0)
            if axis == self.axis:
                if cls.args:
                    return MatrixExpr.of(self, cls)
                else:
                    return self.args
      
    def _hashable_content(self):
        return self._args + (self.axis,)
    
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        return self
    
    def doit(self, **hints):
        if hints.get('deep', True):
            return self.func([arg.doit(**hints) for arg in self.args], **self.kwargs)
        return self

    def _eval_conjugate(self):
        return self.func(*(~arg for arg in self.args), **self.kwargs, evaluate=False)

    def _eval_is_singular(self):
        if len(self.shape) == 2:
            det = self._eval_determinant()
            if det is not None:
                return det.is_zero


class BlockDiagMatrix(MatrixExpr):
    """
    A BlockDiagMatrix is a BlockMatrix with matrices only along the diagonal

    >>> from sympy import MatrixSymbol, BlockDiagMatrix, symbols, Identity
    >>> n, m, l = symbols('n m l')
    >>> X = MatrixSymbol('X', n, n)
    >>> Y = MatrixSymbol('Y', m ,m)
    >>> BlockDiagMatrix(X, Y)
    Matrix([
    [X, 0],
    [0, Y]])

    See Also
    ========
    sympy.matrices.common.diag
    """

    def __new__(cls, *mats):
        return Basic.__new__(BlockDiagMatrix, *mats)

    @property
    def diag(self):
        return self.args

    @property
    def blocks(self):
        from sympy.matrices.immutable import ImmutableDenseMatrix
        mats = self.args
        data = [[mats[i] if i == j else Zeros(mats[i].rows, mats[j].cols)
                        for j in range(len(mats))]
                        for i in range(len(mats))]
        return ImmutableDenseMatrix(data)

    @cacheit
    def _eval_shape(self):
        return (sum(block.rows for block in self.args), sum(block.cols for block in self.args))

    @property
    def blockshape(self):
        n = len(self.args)
        return (n, n)

    @property
    def rowblocksizes(self):
        return [block.rows for block in self.args]

    @property
    def colblocksizes(self):
        return [block.cols for block in self.args]

    def _eval_inverse(self, expand='ignored'):
        return BlockDiagMatrix(*[mat.inverse() for mat in self.args])

    def _blockmul(self, other):
        if (isinstance(other, BlockDiagMatrix) and
                self.colblocksizes == other.rowblocksizes):
            return BlockDiagMatrix(*[a * b for a, b in zip(self.args, other.args)])
        else:
            return BlockMatrix._blockmul(self, other)

    def _blockadd(self, other):
        if (isinstance(other, BlockDiagMatrix) and
                self.blockshape == other.blockshape and
                self.rowblocksizes == other.rowblocksizes and
                self.colblocksizes == other.colblocksizes):
            return BlockDiagMatrix(*[a + b for a, b in zip(self.args, other.args)])
        else:
            return BlockMatrix._blockadd(self, other)


def block_collapse(expr):
    """Evaluates a block matrix expression

    >>> from sympy import MatrixSymbol, BlockMatrix, symbols, \
                          Identity, Matrix, Zeros, block_collapse
    >>> n,m,l = symbols('n m l')
    >>> X = MatrixSymbol('X', n, n)
    >>> Y = MatrixSymbol('Y', m ,m)
    >>> Z = MatrixSymbol('Z', n, m)
    >>> B = BlockMatrix([[X, Z], [Zeros(m, n), Y]])
    >>> print(B)
    Matrix([
    [X, Z],
    [0, Y]])

    >>> C = BlockMatrix([[Identity(n), Z]])
    >>> print(C)
    Matrix([[I, Z]])

    >>> print(block_collapse(C*B))
    Matrix([[X, Z + Z*Y]])
    """
    from sympy.matrices.expressions.matmul import MatMul
    hasbm = lambda expr: isinstance(expr, MatrixExpr) and expr.has(BlockMatrix)
    rule = exhaust(
        bottom_up(exhaust(condition(hasbm, typed(
            {MatAdd: do_one(bc_matadd, bc_block_plus_ident),
             MatMul: do_one(bc_matmul, bc_dist),
             MatPow: bc_matmul,
             Transpose: bc_transpose,
             Inverse: bc_inverse,
             BlockMatrix: do_one(bc_unpack, deblock)})))))
    result = rule(expr)
    doit = getattr(result, 'doit', None)
    if doit is not None:
        return doit()
    else:
        return result


def bc_unpack(expr):
    if expr.blockshape == (1, 1):
        return expr.blocks[0, 0]
    return expr


def bc_matadd(expr):
    args = sift(expr.args, lambda M: isinstance(M, BlockMatrix))
    blocks = args[True]
    if not blocks:
        return expr

    nonblocks = args[False]
    block = blocks[0]
    for b in blocks[1:]:
        block = block._blockadd(b)
    if nonblocks:
        return MatAdd(*nonblocks) + block
    else:
        return block


def bc_block_plus_ident(expr):
    idents = [arg for arg in expr.args if arg.is_Identity]
    if not idents:
        return expr

    blocks = [arg for arg in expr.args if isinstance(arg, BlockMatrix)]
    if (blocks and all(b.structurally_equal(blocks[0]) for b in blocks)
               and blocks[0].is_structurally_symmetric):
        block_id = BlockDiagMatrix(*[Identity(k)
                                        for k in blocks[0].rowblocksizes])
        return MatAdd(block_id * len(idents), *blocks).doit()

    return expr


def bc_dist(expr):
    """ Turn  a*[X, Y] into [a*X, a*Y] """
    factor, mat = expr.as_coeff_mmul()
    if factor != 1 and isinstance(unpack(mat), BlockMatrix):
        B = unpack(mat).blocks
        return BlockMatrix([[factor * B[i, j] for j in range(B.cols)]
                                              for i in range(B.rows)])
    return expr


def bc_matmul(expr):
    if isinstance(expr, MatPow):
        if expr.args[1].is_Integer:
            factor, matrices = (1, [expr.args[0]] * expr.args[1])
        else:
            return expr
    else:
        factor, matrices = expr.as_coeff_matrices()

    i = 0
    while (i + 1 < len(matrices)):
        A, B = matrices[i:i + 2]
        if isinstance(A, BlockMatrix) and isinstance(B, BlockMatrix):
            matrices[i] = A._blockmul(B)
            matrices.pop(i + 1)
        elif isinstance(A, BlockMatrix):
            matrices[i] = A._blockmul(BlockMatrix([[B]]))
            matrices.pop(i + 1)
        elif isinstance(B, BlockMatrix):
            matrices[i] = BlockMatrix([[A]])._blockmul(B)
            matrices.pop(i + 1)
        else:
            i += 1
    from sympy.matrices.expressions.matmul import MatMul
    return MatMul(factor, *matrices).doit()


def bc_transpose(expr):
    return BlockMatrix(block_collapse(expr.arg).blocks.applyfunc(transpose).T)


def bc_inverse(expr):
    expr2 = blockinverse_1x1(expr)
    if expr != expr2:
        return expr2
    return blockinverse_2x2(Inverse(reblock_2x2(expr.arg)))


def blockinverse_1x1(expr):
    if isinstance(expr.arg, BlockMatrix) and expr.arg.blockshape == (1, 1):
        mat = Matrix([[expr.arg.blocks[0].inverse()]])
        return BlockMatrix(mat)
    return expr


def blockinverse_2x2(expr):
    if isinstance(expr.arg, BlockMatrix) and expr.arg.blockshape == (2, 2):
        # Cite: The Matrix Cookbook Section 9.1.3
        [[A, B],
         [C, D]] = expr.arg.blocks.tolist()

        return BlockMatrix([[ (A - B * D.I * C).I, (-A).I * B * (D - C * A.I * B).I],
                            [-(D - C * A.I * B).I * C * A.I, (D - C * A.I * B).I]])
    else:
        return expr


def deblock(B):
    """ Flatten a BlockMatrix of BlockMatrices """
    if not isinstance(B, BlockMatrix) or not B.blocks.has(BlockMatrix):
        return B
    wrap = lambda x: x if isinstance(x, BlockMatrix) else BlockMatrix([[x]])
    bb = B.blocks.applyfunc(wrap)  # everything is a block

    from sympy import Matrix
    try:
        MM = Matrix(0, sum(bb[0, i].blocks.shape[1] for i in range(bb.shape[1])), [])
        for row in range(0, bb.shape[0]):
            M = Matrix(bb[row, 0].blocks)
            for col in range(1, bb.shape[1]):
                M = M.row_join(bb[row, col].blocks)
            MM = MM.col_join(M)

        return BlockMatrix(MM)
    except ShapeError:
        return B


def reblock_2x2(B):
    """ Reblock a BlockMatrix so that it has 2x2 blocks of block matrices """
    if not isinstance(B, BlockMatrix) or not all(d > 2 for d in B.blocks.shape):
        return B

    BM = BlockMatrix  # for brevity's sake
    return BM([[   B.blocks[0, 0], BM(B.blocks[0, 1:])],
               [BM(B.blocks[1:, 0]), BM(B.blocks[1:, 1:])]])


def bounds(sizes):
    """ Convert sequence of numbers into pairs of low-high pairs

    >>> from sympy.matrices.expressions.blockmatrix import bounds
    >>> bounds((1, 10, 50))
    [(0, 1), (1, 11), (11, 61)]
    """
    low = 0
    rv = []
    for size in sizes:
        rv.append((low, low + size))
        low += size
    return rv


def blockcut(expr, rowsizes, colsizes):
    """ Cut a matrix expression into Blocks

    >>> from sympy import ImmutableMatrix, blockcut
    >>> M = ImmutableMatrix(4, 4, range(16))
    >>> B = blockcut(M, (1, 3), (1, 3))
    >>> type(B).__name__
    'BlockMatrix'
    >>> ImmutableMatrix(B.blocks[0, 1])
    Matrix([[1, 2, 3]])
    """

    rowbounds = bounds(rowsizes)
    colbounds = bounds(colsizes)
    from sympy.matrices.expressions.slice import MatrixSlice
    return BlockMatrix([[MatrixSlice(expr, rowbound, colbound)
                         for colbound in colbounds]
                         for rowbound in rowbounds])

# from sympy.core.sympify import converter
# converter[list] = lambda l: BlockMatrix(l)
