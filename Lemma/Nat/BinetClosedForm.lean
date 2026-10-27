import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[binet_closed_form_second_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinetClosedForm.lean)
-/
@[path]
lemma binet_closed_form_second_order
  [Field K]
  {u : ℕ → K}
  {P Q α β : K}
  {n : ℕ}
-- given
  (hα : α ^ 2 - P * α + Q = 0)
  (hβ : β ^ 2 - P * β + Q = 0)
  (hne : α ≠ β)
  (hrec : ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n) :
-- imply
  u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β) := by
-- proof
  have hne' : α - β ≠ 0 := sub_ne_zero.mpr hne
  have key : ∀ m : ℕ, u m * (α - β) =
    (u 1 - β * u 0) * α ^ m - (u 1 - α * u 0) * β ^ m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => ring
    | one => ring
    | more m ih0 ih1 =>
      have r := hrec m
      linear_combination (α - β) * r + P * ih1 - Q * ih0 -
        ((u 1 - β * u 0) * α ^ m) * hα + ((u 1 - α * u 0) * β ^ m) * hβ
  rw [eq_div_iff hne']
  exact key n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
