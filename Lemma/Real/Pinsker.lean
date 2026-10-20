import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.Pinsker
open Finset BigOperators
open MathlibExt.InformationTheory.Pinsker


/--
[csiszar_kullback_pinsker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Pinsker.lean)
-/
@[path]
private lemma csiszar_kullback_pinsker_eq
  [Fintype α] [Nonempty α]
  {p q : α → ℝ}
-- given
  (hp_pos : ∀ a, 0 < p a)
  (hq_pos : ∀ a, 0 < q a)
  (hp_sum : ∑ a : α, p a = 1)
  (hq_sum : ∑ a : α, q a = 1) :
-- imply
  (∑ a : α, |p a - q a|) ^ 2 ≤ 2 * ∑ a : α, p a * Real.log (p a / q a) := by
-- proof
  apply MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker p q hp_pos hq_pos hp_sum hq_sum


-- created on 2026-10-20
