/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/LAdditiveFunction.lean -/


import Def.Algebra.LAdditiveFunction
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

example : IsLAdditive (fun _ : Int ↦ 0) := by
  intro m n
  simp

example {K : Type*} [Ring K] {f : K → K} (h : IsLAdditive f) (m n : K) :
    f (m * n) = f m * n + f n * m :=
  h m n

example {K : Type*} [Ring K] {f : K → K}
    (h : ∀ m n, f (m * n) = f m * n + f n * m) : IsLAdditive f :=
  h

example : ¬ IsLAdditive (fun x : Int ↦ x) := by
  intro h
  have h11 := h 1 1
  norm_num at h11

end MetaMathlibExt
