import Lemma.Vector.GetDiv.eq.DivGetS
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Div.eq.DivDivS.of.Ne_0 |
| comm | Vector.DivDivS.eq.Div.of.Ne_0 |
-/
@[path, comm]
private lemma main
  [CommGroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0)
  (x y : List.Vector α n) :
-- imply
  x / y = x / a / (y / a) := by
-- proof
  ext i
  simp only [HDiv.hDiv, Div.div, List.Vector.get_map₂, List.Vector.get_map]
  apply (div_div_div_cancel_right₀ h _ _).symm


-- created on 2025-12-17
-- updated on 2026-11-20
