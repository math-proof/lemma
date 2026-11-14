import Mathlib

set_option autoImplicit false

namespace FLT.SmoothVectors

def RightTranslationFn (G M : Type*) : Type _ := G → M

namespace RightTranslationFn

variable {G M : Type*}

def mk (f : G → M) : RightTranslationFn G M := f

def toFun (f : RightTranslationFn G M) : G → M := f

@[simp] theorem toFun_mk (f : G → M) : toFun (mk f) = f := rfl

@[simp] theorem mk_toFun (f : RightTranslationFn G M) : mk (toFun f) = f := rfl

theorem ext {f g : RightTranslationFn G M} (h : ∀ x, toFun f x = toFun g x) : f = g :=
  funext h

end RightTranslationFn

end FLT.SmoothVectors
