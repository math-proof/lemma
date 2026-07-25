import sympy.Basic
import sympy.tensor.Basic
import sympy.tensor.functions


@[main]
private lemma main
  [Div α] [Add α] [Zero α]
  [XEq α]
  {x y : Tensor α [n]}
-- given
  (h : y ≈ x) :
-- imply
  let den_x : Tensor α [] := x.sum 0
  let den_y : Tensor α [] := y.sum 0
  y / den_y ≈ x / den_x := by
-- proof
  intro den_x den_y
  simp [den_x, den_y]
  if h_x : den_x = 0 then
    sorry
  else
    have h_x : den_x ≠ 0 := by omega
    sorry


-- created on 2026-07-25
