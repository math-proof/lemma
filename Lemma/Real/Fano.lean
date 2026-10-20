import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.Fano
open Finset BigOperators
open MathlibExt.InformationTheory.Fano


/--
[fano_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Fano.lean)
-/
@[path]
private lemma fano_inequality_general_eq
  [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [DecidableEq α]
  {p : α → β → ℝ}
  {g : β → α}
-- given
  (hp_pos : ∀ a b, 0 < p a b)
  (hp_sum : ∑ a : α, ∑ b : β, p a b = 1)
  (hcard : 2 ≤ Fintype.card α) :
-- imply
  let pY : β → ℝ := by
-- proof
  apply MathlibExt.InformationTheory.Fano.fano_inequality_general p hp_pos hp_sum g hcard

/--
[fano_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Fano.lean)
-/
@[path]
private lemma fano_inequality_eq
  [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [DecidableEq α] [DecidableEq β]
  {p : α → β → ℝ}
  {g : β → α}
-- given
  (hp_pos : ∀ a b, 0 < p a b)
  (hp_sum : ∑ a : α, ∑ b : β, p a b = 1)
  (hcard : 2 ≤ Fintype.card α) :
-- imply
  let pY : β → ℝ := by
-- proof
  apply MathlibExt.InformationTheory.Fano.fano_inequality p hp_pos hp_sum g hcard


-- created on 2026-10-20
