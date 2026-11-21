import Instance.Data.Tensor.Defs.Part2


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Div.eq.DivDivS.of.Ne_0 |
| comm | Tensor.DivDivS.eq.Div.of.Ne_0 |
-/
@[path, comm]
private lemma main
  [CommGroupWithZero α]
  {A : α}
-- given
  (h : A ≠ 0)
  (X Y : Tensor α s) :
-- imply
  X / Y = X / A / (Y / A) := by
-- proof
  simp [HDiv.hDiv, Div.div]
  ext i
  simp only [List.Vector.get_map₂]
  apply (div_div_div_cancel_right₀ h _ _).symm


-- created on 2025-09-26
-- updated on 2026-11-20
