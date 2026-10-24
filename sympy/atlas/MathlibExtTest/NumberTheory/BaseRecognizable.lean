/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BaseRecognizable.lean -/


import sympy.atlas.NumberTheory.BaseRecognizable
import Lemma.Nat.BaseRecognizable

namespace MetaMathlibExt

/- Digits are read most significant first. -/
example : baseWordValue ([1, 0] : List (Fin 2)) = 2 := by decide
example : baseWordValue ([0, 1] : List (Fin 2)) = 1 := by decide
example : baseWordValue ([1, 2, 3] : List (Fin 10)) = 123 := by decide

/- Zero is the empty word, which is canonical. -/
example : baseDigits (k := 10) (by decide) 0 = [] := baseDigits_zero _
example : IsCanonicalBaseWord ([] : List (Fin 10)) := isCanonicalBaseWord_nil

/- Leading zeros are rejected. -/
example : ¬ IsCanonicalBaseWord ([0, 1] : List (Fin 2)) := by simp
example : IsCanonicalBaseWord ([1, 0] : List (Fin 2)) := by simp

/- `baseDigits` is a canonical inverse of `baseWordValue`. -/
example : baseWordValue (baseDigits (k := 10) (by decide) 1234) = 1234 :=
  baseWordValue_baseDigits _ _
example : IsCanonicalBaseWord (baseDigits (k := 7) (by decide) 100) :=
  isCanonicalBaseWord_baseDigits _ _
example (u v : List (Fin 3)) :
    baseWordValue (u ++ v) = baseWordValue u * 3 ^ v.length + baseWordValue v :=
  baseWordValue_append u v

end MetaMathlibExt
