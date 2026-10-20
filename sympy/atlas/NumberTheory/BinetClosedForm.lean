/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinetClosedForm.lean -/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

variable {K : Type*} [Field K]

/-- Generalized Binet closed form: a sequence satisfying
`u (n + 2) = P * u (n + 1) - Q * u n` over a field, whose characteristic
roots `α ≠ β` both satisfy `z ^ 2 - P * z + Q = 0`, is given by
`u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β)`.

Source: Hongshen Chua, "A Study of Second-Order Linear Recurrence
Sequences via Continuants," Journal of Integer Sequences 26 (2023),
Article 23.8.8, Theorem [Binet's formula] (label Th:Binet_Formula),
lines 270–274,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Chua2/chua13.tex>.
Proves `Wanted` entry `binet_closed_form_second_order`. -/
theorem binet_closed_form_second_order
    (u : ℕ → K) (P Q α β : K)
    (hα : α ^ 2 - P * α + Q = 0) (hβ : β ^ 2 - P * β + Q = 0)
    (hne : α ≠ β)
    (hrec : ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n)
    (n : ℕ) :
    u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β) := by
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
