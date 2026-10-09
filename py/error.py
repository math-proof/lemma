import sys

class Cout:
    def __init__(self):
        self._buff = []
 
    def write(self, s):
#         print(s, file=stdout, end='')
        self._buff.append(s)
        
    def clear(self):
        self._buff.clear()
        
    def __str__(self):
        return ''.join(self._buff)

Cout = Cout()

class __LINE__:

    def __repr__(self):
        try:
            raise Exception
        except:
            return str(sys.exc_info()[2].tb_frame.f_back.f_lineno)

 
__LINE__ = __LINE__()
