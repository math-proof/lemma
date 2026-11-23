module

public import Mathlib

@[expose] public section

set_option autoImplicit false

namespace FLT.SmoothVectors

def RightTranslationFn (G M : Type*) : Type _ := G → M

namespace RightTranslationFn

variable {G M : Type*}

def mk (f : G → M) : RightTranslationFn G M := f

def toFun (f : RightTranslationFn G M) : G → M := f

end RightTranslationFn

end FLT.SmoothVectors

end
