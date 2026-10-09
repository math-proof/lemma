from py import computed, equal_range, binary_search

class SymbolicSet:
    is_EmptySet = False
    
    is_Range = False
    
    is_Union = False
    
    def symmetric_difference(self, that):
        return (self | that) - (self & that)


class EmptySet(SymbolicSet):
    is_EmptySet = True
    
    @property
    def card(self):
        return 0
    
    def __eq__(self, that):
        return that is None or that.is_EmptySet
    
    def __sub__(self, that):
        return self
    
    def __add__(self, offset):
        return self
    
    def __and__(self, offset):
        return self
    
    def __or__(self, that):
        return that

    def symmetric_difference(self, that):
        return that

    @property
    def dict(self):
        return {}

    def __str__(self):
        return '{}'

    __repr__ = __str__

    def __bool__(self):
        return False
    
    __nonzero__ = __bool__
    
    #lhs in self
    def __contains__(self, lhs):
        if lhs.is_EmptySet:
            return True
        
    def __iter__(self):  # Get iterator object on iter
        return RangeIterator(Range(0, 0))


class Union(SymbolicSet):
    is_Union = True
    
    @staticmethod
    def new(*arguments):
        if not arguments:
            return EmptySet()
            
        if len(arguments) == 1:
            return arguments[0]
            
        return Union(*arguments)
        
    def __init__(self, *args, **kwargs):
        if not args:
            args = kwargs['args']
            args = [Range(**arg) for arg in args]

        #assert not any(arg.is_EmptySet or arg.is_Union for arg in args)
        self.args = args
    
    @computed
    def card(self):
        card = 0
        for arg in self.args:
            card += arg.card
        return card
    
    def __and__(self, that):
        if that.is_EmptySet:
            return that

        args = []
        if that.is_Range:
            for i in range(*equal_range(self.args, that)):
                arg = self.args[i]
                arg &= that
                assert arg.is_Range
                    
                args.append(arg)
        else:
            for arg in self.args:
                arg &= that
                if arg.is_EmptySet:
                    continue
                    
                if arg.is_Union:
                    args += arg.args
                else:
                    args.append(arg)
            
        return Union.new(*args)
    
    def __eq__(self, that):
        if that and that.is_Union and len(self.args) == len(that.args):
            for i in range(len(self.args)):
                if self.args[i] != that.args[i]:
                    return False
            return True
    
    def __sub__(self, that):
        args = []
        for arg in self.args:
            arg -= that
            if arg.is_EmptySet:
                continue
                
            if arg.is_Union:
                args += arg.args
            else:
                args.append(arg)
        
        if not args:
            return EmptySet()
            
        if len(args) == 1:
            return args[0]
            
        return Union(*args)
    
    def __add__(self, offset):
        return Union(*map(lambda el : el + offset, self.args))

    def __or__(self, that):
        if that.is_EmptySet:
            return self
        
        if that.is_Range:
            for i in range(len(self.args)):
                arg = self.args[i]
                arg |= that
                if arg.is_Range:
                    args = [*self.args]
                    del args[i]
                    if len(args) == 1:
                        return args[0] | arg
                    
                    return Union(*args) | arg
            
            args = [*self.args]
            
            index = binary_search(args, that)
            
            args.insert(index, that)
            
            return Union(*args)

        for arg in self.args:
            that |= arg
        return that

    def union_without_merging(self, that):
        if that.is_EmptySet:
            return self
        
        if that.is_Range:
            for arg in self.args:
                that -= arg
            
            if that.is_EmptySet:
                return self
            
            if that.is_Range:
                that = [that]
            else:
                that = that.args
                
            args = [*self.args]
            
            for that in that:
                index = binary_search(args, that)
                args.insert(index, that)
            
            return Union(*args)
        
        if that.is_Union:
            for arg in that.args:
                assert arg.is_Range
                self = self.union_without_merging(arg)
                
            return self
        raise
    
    @property
    def dict(self):
        return dict(args=[*map(lambda arg: arg.dict, self.args)])

    def __str__(self):
        return ' | '.join((str(arg) for arg in self.args))

    __repr__ = __str__

    #lhs in self
    def __contains__(self, lhs):
        if isinstance(lhs, int) or lhs.is_Range:
            return any(lhs in arg for arg in self.args)
        
        if lhs.is_EmptySet:
            return True
        
        if lhs.is_Union:
            return all(arg in self for arg in lhs.args)


class Range(SymbolicSet):
    is_Range = True
    
    def __init__(self, start, stop):
        self.start = start
        self.stop = stop
    
    @property
    def args(self):
        return [self.start, self.stop]
    
    def __and__(self, that):
        if that.is_Union:
            return that & self
        
        [start, stop] = that.args
        
        if start >= self.stop or stop <= self.start:
            return EmptySet()
            
        return Range(max(self.start, start), min(self.stop, stop))

    def __eq__(self, that):
        if that and that.is_Range:
            return self.start == that.start and self.stop == that.stop
    
    def __or__(self, that):
        if that.is_Range:
            [start, stop] = that.args
            if start > self.stop:
                return Union(self, that)
                
            if stop < self.start:
                return Union(that, self)
                
            return Range(min(self.start, start), max(self.stop, stop))
        
        if that.is_EmptySet:
            return self
            
        return that | self
    
    def union_without_merging(self, that):
        if that.is_EmptySet:
            return self
            
        if that.is_Range:
            [start, stop] = that.args
            if start >= self.stop:
                return Union(self, that)
                
            if stop <= self.start:
                return Union(that, self)
            
            mid = self & that
            assert mid
            
            lhs = self - that
            rhs = that - self
            
            if not rhs:
                return mid.union_without_merging(lhs)
            
            if not lhs:
                return mid.union_without_merging(rhs)
            
            if lhs.start > rhs.start:
                lhs, rhs = rhs, lhs
            return Union(lhs, mid, rhs)
        
        return that.union_without_merging(self)
    
    def __sub__(self, that):
        if that.start >= self.stop:
            return self
        
        if that.start > self.start:
            if that.stop >= self.stop:
                return Range(self.start, that.start)
                
            return Union(Range(self.start, that.start), Range(that.stop, self.stop))
        else:
            if that.stop >= self.stop:
                return EmptySet()
                
            if that.stop > self.start:
                return Range(that.stop, self.stop)
            
            return Range(self.start, self.stop)
    
    @computed
    def card(self):
        return self.stop - self.start
    
    def __add__(self, offset):
        return Range(self.start + offset, self.stop + offset)
    
    @property
    def dict(self):
        return dict(start=self.start, stop=self.stop)
            
    def __str__(self):
        return f"[{self.start}; {self.stop})"

    __repr__ = __str__
    
    #lhs in self
    def __contains__(self, lhs):
        if isinstance(lhs, int):
            return lhs >= self.start and lhs < self.stop
        
        if lhs.is_EmptySet:
            return True
        
        if lhs.is_Range:
            return lhs.start >= self.start and lhs.stop <= self.stop
        
        if lhs.is_Union:
            return all(arg in self for arg in lhs.args)
    
    def batches(self, step):
        start, stop = self.start, self.stop
        interval = []
        for i in range(start, stop, step):
            interval.append(Range(i, min(i + step, stop)))
                
        return interval

    def __lt__(self, that):
        return self.stop <= that.start
    
    def __gt__(self, that):
        return self.start >= that.stop

    def __iter__(self):  # Get iterator object on iter
        return RangeIterator(self)


class RangeIterator:
    def __init__(self, range):
        self.start = range.start
        self.stop = range.stop
        self.current = range.start
    
    def __next__(self):
        if self.current >= self.stop:
            raise StopIteration
        
        current = self.current
        self.current += 1
        return current
    

class Range2D(SymbolicSet):
    is_Range2D = True
    
    def __init__(self, x, y, width, height):
        self.x = x
        self.y = y
        self.width = width
        self.height = height
    
    @property
    def x_stop(self):
        return self.x + self.width

    @property
    def y_stop(self):
        return self.y + self.height

    @property
    def args(self):
        return [self.x, self.y, self.x_stop, self.y_stop]
    
    def __and__(self, that):
        if that.is_Union:
            return that & self
        
        x, y, x_stop, y_stop = that.args
        
        if x >= self.x_stop or x_stop <= self.x or y >= self.y_stop or y_stop <= self.y:
            return EmptySet()

        x = max(self.x, x)
        x_stop = min(self.x_stop, x_stop)
        
        y = max(self.y, y)
        y_stop = min(self.y_stop, y_stop)
        
        width = x_stop - x
        height = y_stop - y
        return Range2D(x, y, width, height)

    def __eq__(self, that):
        if that and that.is_Range2D:
            return self.x == that.x and self.width == that.width and self.y == that.y and self.height == that.height
    
    def __or__(self, that):
        if that.is_Range2D:
            x, y, x_stop, y_stop = that.args
            if x == self.x and x_stop == self.x_stop:
                if y == self.y_stop:
                    return Range2D(self.x, self.y, self.width, self.height + that.height)
                if self.y == y_stop:
                    return Range2D(x, y, self.width, self.height + that.height)

            elif y == self.y and y_stop == self.y_stop:
                if x == self.x_stop:
                    return Range2D(self.x, self.y, self.width + that.width, self.height)
                if self.x == x_stop:
                    return Range2D(x, y, self.width + that.width, self.height)
                
            return Union(self, that)

        if that.is_EmptySet:
            return self
            
        return that | self
    
    def __sub__(self, that):
        if that.is_Range2D:
            if that.x >= self.x_stop or that.y >= self.y_stop or that.x_stop <= self.x or that.y_stop <= self.y:
                return self
            
            # that.x < self.x_stop && that.x_stop > self.x
            # that.y < self.y_stop && that.y_stop > self.y
            if that.x <= self.x:
                if that.x_stop < self.x_stop:
                    #that.x <= self.x && that.x_stop < self.x_stop
                    if that.y <= self.y:
                        if that.y_stop < self.y_stop:
                            #that.y <= self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, that.y_stop, self.width, self.y_stop - that.y),
                                Range2D(that.x_stop, self.y, self.x_stop - that.x_stop, that.y_stop - self.y))
                        else:
                            #that.y <= self.y && that.y_stop >= self.y_stop
                            return Range2D(that.x_stop, self.y, self.x_stop - that.x_stop, self.height)
                    else :
                        if that.y_stop < self.y_stop:
                            #that.y > self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y_stop, self.width, self.y_stop - that.y_stop),
                                Range2D(that.x_stop, that.y, self.x_stop - that.x_stop, that.height))
                        else:
                            #that.y > self.y && that.y_stop >= self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(that.x_stop, that.y, self.x_stop - that.x_stop, self.y_stop - that.y))
                else :
                    #that.x <= self.x && that.x_stop >= self.x_stop
                    if that.y <= self.y:
                        if that.y_stop < self.y_stop:
                            #that.y <= self.y && that.y_stop < self.y_stop
                            return Range2D(self.x, that.y_stop, self.width, that.y_stop - self.y);
                        else:
                            #that.y <= self.y && that.y_stop >= self.y_stop
                            return EmptySet()
                    else :
                        if that.y_stop < self.y_stop:
                            #that.y > self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y_stop, self.width, self.y_stop - that.y_stop))
                        else :
                            #that.y > self.y && that.y_stop >= self.y_stop
                            return Range2D(self.x, self.y, self.width, that.y - self.y)
            else :
                if that.x_stop < self.x_stop:
                    #that.x > self.x && that.x_stop < self.x_stop
                    if that.y <= self.y:
                        if that.y_stop < self.y_stop:
                            #that.y <= self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, that.x - self.x, self.height),
                                Range2D(that.x, that.y_stop, self.x_stop - that.x, self.y_stop - that.y_stop),
                                Range2D(that.x_stop, self.y, self.x_stop - that.x_stop, that.y_stop - self.y))
                        else :
                            #that.y <= self.y && that.y_stop >= self.y_stop
                            return Union(
                                Range2D(self.x, self.y, that.x - self.x, self.height),
                                Range2D(that.x_stop, self.y, self.x_stop - that.x_stop, that.height))
                    else :
                        if that.y_stop < self.y_stop:
                            #that.y > self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y, that.x - self.x, self.y_stop - that.y),
                                Range2D(that.x, that.y_stop, self.x_stop - self.x, self.y_stop - that.y_stop),
                                Range2D(that.x_stop, that.y, self.x_stop - that.x_stop, that.height))
                        else :
                            #that.y > self.y && that.y_stop >= self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y, that.x - self.x, self.y_stop - that.y),
                                Range2D(that.x_stop, that.y, self.x_stop - that.x_stop, self.y_stop - that.y))
                else :
                    #that.x > self.x && that.x_stop >= self.x_stop
                    if that.y <= self.y:
                        if that.y_stop < self.y_stop:
                            #that.y <= self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, that.x - self.x, self.height),
                                Range2D(that.x, that.y_stop, self.x_stop - that.x, self.y_stop - that.y_stop));
                        else:
                            #that.y <= self.y && that.y_stop >= self.y_stop
                            return Range2D(self.x, self.y, that.x - self.x, self.height);
                    else:
                        if that.y_stop < self.y_stop:
                            #that.y > self.y && that.y_stop < self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y, that.x - self.x, self.y_stop - that.y),
                                Range2D(that.x, that.y_stop, self.x_stop - self.x, self.y_stop - that.y_stop))
                        else:
                            #that.y > self.y && that.y_stop >= self.y_stop
                            return Union(
                                Range2D(self.x, self.y, self.width, that.y - self.y),
                                Range2D(self.x, that.y, that.x - self.x, self.y_stop - that.y))
                            
        elif that.is_EmptySet:
            return self
        elif that.is_Union:
            for region in that.args:
                self -= region
            
            return self
    
    @computed
    def card(self):
        return self.width * self.height
    
    def __add__(self, offset_x, offset_y):
        return Range2D(self.x + offset_x, self.y + offset_y, self.width, self.height);
    
    @property
    def dict(self):
        return dict(start=self.start, stop=self.stop)
            
    def __str__(self):
        return f"[{self.x}, {self.y}, {self.width}, {self.height}]"

    __repr__ = __str__
    
    #lhs in self
    def __contains__(self, lhs):
        if isinstance(lhs, (list, tuple)):
            x, y = lhs
            return x >= self.x and y < self.x_stop and y >= self.y and y < self.y_stop
        
        if lhs.is_EmptySet:
            return True
        
        if lhs.is_Range2D:
            x, y, x_stop, y_stop = self.args
            return x >= self.x and x_stop <= self.x_stop and y >= self.y and y_stop <= self.y_stop
        
        if lhs.is_Union:
            return all(arg in self for arg in lhs.args)
       
            
if __name__ == '__main__':
    ...
    
