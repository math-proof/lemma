module

public import Mathlib

public section

set_option autoImplicit false

namespace FLT.SmoothVectors


@[simp] public theorem toFun_mk (f : G → M) : toFun (mk f) = f := rfl


@[simp] public theorem mk_toFun (f : RightTranslationFn G M) : mk (toFun f) = f := rfl


public theorem ext {f g : RightTranslationFn G M} (h : ∀ x, toFun f x = toFun g x) : f = g :=
  funext h

end RightTranslationFn

end FLT.SmoothVectors
